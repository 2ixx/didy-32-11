#include "pch.h"
#include "ProcessEventHook.h"
#include <cstdarg>
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <cmath>
#include <mutex>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

// ---- Remix SDK compatibility shim (replaces helpers from the old SDK wrapper) ----
static uint32 GetStructOffset(const UStruct* Struct, const char* Name)
{
    for (; Struct; Struct = Struct->SuperStruct)
    {
        auto Link = uint64(Struct->ChildProperties);

        for (auto Field = Link ? (FField*)(~_rotr64(Link ^ 0xAC0E7F64ull, 0x10)) : nullptr; Field; Field = Field->GetNext())
        {
            if (Field->Name.ToString() == Name)
                return (uint32)(((FProperty*)Field)->Offset ^ 0xE026103B);
        }
    }

    return (uint32)-1;
}

static uint32 GetObjectOffset(const UObject* Object, const char* Name)
{
    return Object && Object->Class ? GetStructOffset((const UStruct*)Object->Class, Name) : (uint32)-1;
}

static UClass* FindClass(const char* Name)
{
    return UObject::FindClassFast(Name);
}

static const uintptr_t ImageBase = (uintptr_t)GetModuleHandleA(nullptr);

// MinHook wrapper: Hook(address, detour, original)
template <typename TFn>
static bool Hook(uintptr_t Address, TFn* Detour, TFn*& Original)
{
    static bool bInitialized = false;

    if (!bInitialized)
    {
        auto Status = MH_Initialize();
        bInitialized = Status == MH_OK || Status == MH_ERROR_ALREADY_INITIALIZED;
    }

    if (!bInitialized)
        return false;

    auto Create = MH_CreateHook((LPVOID)Address, (LPVOID)Detour, (LPVOID*)&Original);

    if (Create != MH_OK)
    {
        PumpkinProjectile::Log("ProcessEvent", "MH_CreateHook failed: %s", MH_StatusToString(Create));
        return false;
    }

    auto Enable = MH_EnableHook((LPVOID)Address);

    if (Enable != MH_OK)
    {
        PumpkinProjectile::Log("ProcessEvent", "MH_EnableHook failed: %s", MH_StatusToString(Enable));
        return false;
    }

    return true;
}
// ----------------------------------------------------------------------------------

namespace
{
    void (*ProcessEventOG)(UObject*, UFunction*, void*) = nullptr;

    enum EFnFlags : uint32
    {
        FnJumpCollision = 1,
        FnHit = 2,
        FnOverlap = 4,
        FnCharTick = 8,
        FnScan = 16,
        FnReady = 32
    };

    struct FFnInfo
    {
        uint32 Flags = 0;
        ULONGLONG Calls = 0;
    };

    struct FClassInfo
    {
        bool bActor = false;
        bool bCharacter = false;
        bool bProjectile = false;
        bool bFireMesh = false;
        bool bOffRoadTire = false;
        bool bTowerGrenade = false;
        bool bHookBoss = false;
        bool bSkipReplace = false;
        std::string Name;
    };

    std::mutex CacheMutex;
    std::unordered_map<const UFunction*, FFnInfo> FnCache;
    std::unordered_map<const UClass*, FClassInfo> ClassCache;
    std::unordered_set<const UObject*> ScannedActors;
    std::vector<AActor*> FireActorsToDestroy;
    ULONGLONG LastDump = 0;
    int32 DistinctLogged = 0;
    bool bInHandler = false;
    FVector LastGoodVelocity;

    template <typename TString>
    bool Contains(const TString& Text, const char* Part)
    {
        return Text.find(Part) != TString::npos;
    }

    bool IsLWC()
    {
        return true /* 32.11 uses LWC doubles */;
    }

    struct FCall
    {
        UObject* Target = nullptr;
        UFunction* Fn = nullptr;
        uint8 Buf[0x200] = {};

        FCall(UObject* InTarget, const char* Name)
        {
            Target = InTarget;
            Fn = InTarget ? InTarget->Class->FindFunction(Name) : nullptr;

            if (Fn && ((const UStruct*)Fn)->Size > (int32)sizeof(Buf))
                Fn = nullptr;
        }

        bool Ok() const
        {
            return Fn != nullptr;
        }

        bool SetRaw(const char* Param, const void* Data, size_t Size)
        {
            if (!Fn)
                return false;

            auto Offset = GetStructOffset((const UStruct*)Fn, Param);

            if (Offset == (uint32)-1 || Offset + Size > sizeof(Buf))
                return false;

            memcpy(Buf + Offset, Data, Size);
            return true;
        }

        bool GetRaw(const char* Param, void* Data, size_t Size) const
        {
            if (!Fn)
                return false;

            auto Offset = GetStructOffset((const UStruct*)Fn, Param);

            if (Offset == (uint32)-1 || Offset + Size > sizeof(Buf))
                return false;

            memcpy(Data, Buf + Offset, Size);
            return true;
        }

        template <typename T>
        bool Set(const char* Param, const T& Value)
        {
            return SetRaw(Param, &Value, sizeof(T));
        }

        template <typename T>
        T Get(const char* Param) const
        {
            T Value{};
            GetRaw(Param, &Value, sizeof(T));
            return Value;
        }

        bool SetVector(const char* Param, const FVector& Value)
        {
            return SetRaw(Param, &Value, sizeof(FVector));
        }

        FVector GetVector(const char* Param) const
        {
            FVector Value;
            GetRaw(Param, &Value, sizeof(FVector));
            return Value;
        }

        bool Call()
        {
            if (!Fn || !Target)
                return false;

            Target->ProcessEvent(Fn, Buf);
            return true;
        }
    };

    template <typename T>
    T ReadParam(UFunction* Function, void* Params, const char* Name)
    {
        T Value{};
        auto Offset = GetStructOffset((const UStruct*)Function, Name);

        if (Params && Offset != (uint32)-1)
            memcpy(&Value, (uint8*)Params + Offset, sizeof(T));

        return Value;
    }

    FVector ReadVectorParam(UFunction* Function, void* Params, const char* Name)
    {
        FVector Value;
        auto Offset = GetStructOffset((const UStruct*)Function, Name);

        if (Params && Offset != (uint32)-1)
            memcpy(&Value, (uint8*)Params + Offset, sizeof(FVector));

        return Value;
    }

    template <typename T>
    T GetProp(UObject* Object, const char* Name, T Default = T{})
    {
        if (!Object)
            return Default;

        auto Offset = GetObjectOffset(Object, Name);

        if (Offset == (uint32)-1)
            return Default;

        return *(T*)(__int64(Object) + Offset);
    }

    template <typename T>
    bool SetProp(UObject* Object, const char* Name, T Value)
    {
        if (!Object)
            return false;

        auto Offset = GetObjectOffset(Object, Name);

        if (Offset == (uint32)-1)
            return false;

        *(T*)(__int64(Object) + Offset) = Value;
        return true;
    }

    UObject* GetComponentByClass(UObject* Actor, const UClass* Class)
    {
        if (!Class)
            return nullptr;

        FCall Call(Actor, "GetComponentByClass");

        if (!Call.Ok())
            return nullptr;

        Call.Set("ComponentClass", Class);
        Call.Call();
        return Call.Get<UObject*>("ReturnValue");
    }

    void LaunchCharacter(UObject* Character, double X, double Y, double Z)
    {
        FCall Call(Character, "LaunchCharacter");

        if (!Call.Ok())
            return;

        Call.SetVector("LaunchVelocity", FVector(X, Y, Z));
        Call.Set("bXYOverride", true);
        Call.Set("bZOverride", true);
        Call.Call();
    }

    const UClass* ClassCharacter()
    {
        static const UClass* Class = FindClass("Character");
        return Class;
    }

    const UClass* ClassProjectile()
    {
        static const UClass* Class = FindClass("FortProjectileBase");
        return Class;
    }

    const UClass* ClassActor()
    {
        static const UClass* Class = FindClass("Actor");
        return Class;
    }

    FClassInfo& GetClassInfo(UObject* Object)
    {
        static FClassInfo None;
        auto Class = Object->Class;

        if (!Class)
            return None;

        auto Found = ClassCache.find(Class);

        if (Found != ClassCache.end())
            return Found->second;

        FClassInfo Info;
        Info.Name = Class->Name.ToString().c_str();
        Info.bActor = Object->IsA(ClassActor());
        Info.bCharacter = Object->IsA(ClassCharacter());
        Info.bProjectile = Object->IsA(ClassProjectile());
        Info.bFireMesh = Contains(Info.Name, "BGA_CurieFireMesh_FringePlank__C");
        Info.bOffRoadTire = Contains(Info.Name, "B_Prj_ValetMod_OffRoadTire");
        Info.bTowerGrenade = Contains(Info.Name, "B_Prj_Athena_SuperTowerGrenade_A");
        Info.bHookBoss = Contains(Info.Name, "B_Prj_Hook_Boss_C");

        static const char* SkipReplace[] = { "B_Prj_Ranged_PumpkinRocket_Athena", "B_Prj_Ranged_Rocket_Athena", "Prj_Athena_HappyGhost_C", "B_Prj_Bullet_Sniper_C", "B_Prj_Bullet_Sniper_Heavy_C",
                                             "Heavy", "B_Prj_Athena_IceGrenade_C", "Snow", "B_Prj_Athena_ShockGrenade_C", "Car", "Boat", "UFO", "ufo", "Saucer", "Nevada", "boat",
                                             "B_Prj_Athena_KnockGrenade_C", "AGID_SneakySnowmanV2", "B_Prj_ValetMod_OffRoadTire_C", "B_Prj_Athena_SuperTowerGrenade_A" };

        for (auto Part : SkipReplace)
            if (Contains(Info.Name, Part))
                Info.bSkipReplace = true;

        return ClassCache.emplace(Class, Info).first->second;
    }

    FFnInfo& GetFnInfo(UObject* Object, UFunction* Function)
    {
        auto Found = FnCache.find(Function);

        if (Found != FnCache.end())
        {
            Found->second.Calls++;
            return Found->second;
        }

        FFnInfo Info;
        Info.Calls = 1;
        auto Name = Function->Name.ToString();

        if (Contains(Name, "BndEvt__Jump_Collision"))
            Info.Flags |= FnJumpCollision;

        if (Name == "ReceiveHit")
            Info.Flags |= FnHit;

        if (Name == "ReceiveActorBeginOverlap")
            Info.Flags |= FnOverlap;

        if (Contains(Name, "ReceiveTick") || Contains(Name, "PlayerTick") || Name == "UpdatePreviousPositionAndVelocity")
            Info.Flags |= FnCharTick;

        if (Contains(Name, "Tick") || Name == "ReceiveBeginPlay" || Name == "ReadyToRun")
            Info.Flags |= FnScan;

        if (Name == "ReadyToRun" || Name == "OnPostInit" || Name == "InitializeProjectile" || Name == "ReceiveBeginPlay")
            Info.Flags |= FnReady;

        if (DistinctLogged++ < 6000)
            PumpkinProjectile::Log("ProcessEvent", "new %s.%s on %s flags=%u", Function->Outer ? Function->Outer->Name.ToString().c_str() : "null", Name.c_str(), Object->Name.ToString().c_str(), Info.Flags);

        return FnCache.emplace(Function, Info).first->second;
    }

    void DumpTop()
    {
        ULONGLONG Now = GetTickCount64();

        if (!LastDump)
            LastDump = Now;

        if (Now - LastDump < 60000)
            return;

        LastDump = Now;

        std::vector<std::pair<ULONGLONG, const UFunction*>> Sorted;

        for (auto& [Key, Info] : FnCache)
            Sorted.push_back({ Info.Calls, Key });

        std::sort(Sorted.begin(), Sorted.end(), [](auto& A, auto& B) { return A.first > B.first; });

        PumpkinProjectile::Log("ProcessEvent", "distinct functions so far: %d", (int)Sorted.size());

        for (size_t i = 0; i < Sorted.size() && i < 20; i++)
            PumpkinProjectile::Log("ProcessEvent", "top %d: %s.%s calls=%llu", (int)i + 1, Sorted[i].second->Outer ? Sorted[i].second->Outer->Name.ToString().c_str() : "null",
                Sorted[i].second->Name.ToString().c_str(), Sorted[i].first);
    }

    void SetCollisionResponseAll(UObject* Component, uint8 Response)
    {
        if (!Component)
            return;

        FCall Call(Component, "SetCollisionResponseToAllChannels");
        Call.Set("NewResponse", Response);
        Call.Call();
    }

    void HandleFireMesh(UObject* Object)
    {
        auto Actor = (AActor*)Object;

        if (std::find(FireActorsToDestroy.begin(), FireActorsToDestroy.end(), Actor) == FireActorsToDestroy.end())
        {
            PumpkinProjectile::Log("ProcessEvent", "fire mesh found %s", Object->Name.ToString().c_str());
            FireActorsToDestroy.push_back(Actor);
        }
    }

    void FlushFireMeshes()
    {
        for (auto Actor : FireActorsToDestroy)
        {
            if (!Actor)
                continue;

            auto Name = Actor->Name.ToString();
            Actor->K2_DestroyActor();
            PumpkinProjectile::Log("ProcessEvent", "destroyed fire mesh %s", Name.c_str());
        }

        FireActorsToDestroy.clear();
    }

    void ScanUmbrella(UObject* Object)
    {
        if (!ScannedActors.insert(Object).second)
            return;

        FCall Call(Object, "K2_GetComponentsByClass");

        if (!Call.Ok())
            return;

        static const UClass* PrimitiveClass = FindClass("PrimitiveComponent");
        Call.Set("ComponentClass", PrimitiveClass);
        Call.Call();

        auto Offset = GetStructOffset((const UStruct*)Call.Fn, "ReturnValue");

        if (Offset == (uint32)-1)
            return;

        auto& Components = *(TArray<UObject*>*)(Call.Buf + Offset);

        for (int32 i = 0; i < Components.Num(); i++)
        {
            auto Component = Components[i];

            if (!Component || !Contains(Component->Name.ToString(), "Jump_Collision"))
                continue;

            FCall Scale(Component, "SetRelativeScale3D");

            if (Scale.Ok())
            {
                Scale.SetVector("NewScale3D", FVector(1.5, 1.5, 4.0));
                Scale.Call();
                PumpkinProjectile::Log("ProcessEvent", "expanded Jump_Collision hitbox upwards for %s", Object->Name.ToString().c_str());
            }

            break;
        }
    }

    void UpdateCharacterVelocity(UObject* Object)
    {
        FCall Call(Object, "GetVelocity");

        if (!Call.Ok())
            return;

        Call.Call();
        auto Velocity = Call.GetVector("ReturnValue");

        if (Velocity.X * Velocity.X + Velocity.Y * Velocity.Y > 500.0)
            LastGoodVelocity = Velocity;
    }

    void HandleJumpCollision(UFunction* Function, void* Params)
    {
        auto OtherActor = ReadParam<UObject*>(Function, Params, "OtherActor");

        if (!OtherActor || !OtherActor->IsA(ClassCharacter()))
            return;

        LaunchCharacter(OtherActor, LastGoodVelocity.X, LastGoodVelocity.Y, 7500.0);
        PumpkinProjectile::Log("ProcessEvent", "jump collision launch with velocity %.0f %.0f", (double)LastGoodVelocity.X, (double)LastGoodVelocity.Y);
    }

    UObject* FindWorld(UObject* Object);
    UObject* GetGameplayStatics();

    // GameplayStatics::GetAllActorsOfClass through ProcessEvent; the caller frees Out.
    void GetAllActors(UObject* WorldContext, const UClass* ActorClass, TArray<AActor*>& Out)
    {
        auto World = FindWorld(WorldContext);
        auto Statics = GetGameplayStatics();

        if (!World || !Statics)
            return;

        FCall Call(Statics, "GetAllActorsOfClass");

        if (!Call.Ok())
            return;

        Call.Set("WorldContextObject", World);
        Call.Set("ActorClass", ActorClass);
        Call.Call();

        auto Offset = GetStructOffset((const UStruct*)Call.Fn, "OutActors");

        if (Offset == (uint32)-1)
            return;

        memcpy(&Out, Call.Buf + Offset, sizeof(TArray<AActor*>));
    }

    void HandleTowerGrenadeHit(UObject* Object, const FVector& HitLocation)
    {
        FCall VelocityCall(Object, "K2_GetActorVelocity");
        FVector Velocity;

        if (VelocityCall.Ok())
        {
            VelocityCall.Call();
            Velocity = VelocityCall.GetVector("ReturnValue");
        }

        double Speed = Velocity.Magnitude();
        double DirX = 0.0, DirY = 0.0;

        if (Speed > 0.0)
        {
            DirX = Velocity.X / Speed;
            DirY = Velocity.Y / Speed;
        }

        double Horizontal = (double)((rand() % 15001) + 10000);
        double Vertical = (double)((rand() % 10001) + 10000);

        TArray<AActor*> Actors;
        GetAllActors(Object, ClassCharacter(), Actors);

        for (int32 i = 0; i < Actors.Num(); i++)
        {
            auto Actor = Actors[i];

            if (Actor && Actor->K2_GetActorLocation().GetDistanceTo(HitLocation) <= 200.0)
                LaunchCharacter(Actor, DirX * Horizontal, DirY * Horizontal, Vertical);
        }

        Actors.Free();
    }

    void HandleOffRoadTireHit(UObject* Object, UObject* HitActor, UObject* HitComp, const FClassInfo& Info)
    {
        auto MovementComponent = GetComponentByClass(Object, FindClass("ProjectileMovementComponent"));

        if (MovementComponent)
        {
            SetProp<float>(MovementComponent, "InitialSpeed", 8000.f);
            SetProp<float>(MovementComponent, "MaxSpeed", 8000.f);
            SetProp<float>(MovementComponent, "Bounciness", 0.4f);
            SetProp<float>(MovementComponent, "Friction", 0.8f);
        }

        auto Capsule = GetComponentByClass(Object, FindClass("CapsuleComponent"));

        if (Capsule)
        {
            SetProp<float>(Capsule, "CapsuleHalfHeight", 45.f);
            SetProp<float>(Capsule, "CapsuleRadius", 45.f);

            FCall ObjectType(Capsule, "SetCollisionObjectType");
            ObjectType.Set<uint8>("Channel", 21);
            ObjectType.Call();

            FCall Visibility(Capsule, "SetCollisionResponseToChannel");
            Visibility.Set<uint8>("Channel", 2);
            Visibility.Set<uint8>("NewResponse", 0);
            Visibility.Call();

            FCall Camera(Capsule, "SetCollisionResponseToChannel");
            Camera.Set<uint8>("Channel", 3);
            Camera.Set<uint8>("NewResponse", 0);
            Camera.Call();
        }

        auto& HitInfo = GetClassInfo(HitActor);
        bool bIsVehicle = HitActor->IsA(FindClass("FortAthenaVehicle")) || Contains(HitActor->Name.ToString(), "Vehicle");

        if (!bIsVehicle && HitInfo.bActor && HitActor->IsA(FindClass("Pawn")))
            return;

        if (HitActor->IsA(FindClass("BuildingSMActor")) && GetProp<bool>(HitActor, "bPlayerPlaced", false))
            return;

        FCall Simulate(HitComp, "SetSimulatePhysics");
        Simulate.Set("bSimulate", true);
        Simulate.Call();

        FCall Collision(HitComp, "SetCollisionEnabled");
        Collision.Set<uint8>("NewType", 3);
        Collision.Call();

        SetCollisionResponseAll(HitComp, 2);

        FCall Location(HitComp, "K2_GetComponentLocation");
        Location.Call();
        FVector CompLocation = Location.GetVector("ReturnValue");

        auto Instigator = GetProp<UObject*>(Object, "Instigator");
        FVector InstigatorLocation;
        double PlayerPitch = 0.0;

        if (Instigator)
        {
            FCall InstigatorLocationCall(Instigator, "K2_GetActorLocation");
            InstigatorLocationCall.Call();
            InstigatorLocation = InstigatorLocationCall.GetVector("ReturnValue");

            FCall Rotation(Instigator, "GetControlRotation");

            if (Rotation.Ok())
            {
                Rotation.Call();
                auto Offset = GetStructOffset((const UStruct*)Rotation.Fn, "ReturnValue");
                bool bLWC = IsLWC() /* 32.11 uses LWC doubles */;

                if (Offset != (uint32)-1)
                {
                    PlayerPitch = bLWC ? *(double*)(Rotation.Buf + Offset) : (double)*(float*)(Rotation.Buf + Offset);

                    if (PlayerPitch > 180.0)
                        PlayerPitch -= 360.0;
                }
            }
        }

        double DeltaX = CompLocation.X - InstigatorLocation.X;
        double DeltaY = CompLocation.Y - InstigatorLocation.Y;
        double Distance2D = std::sqrt(DeltaX * DeltaX + DeltaY * DeltaY);
        double DirX = Distance2D > 0.0 ? DeltaX / Distance2D : 1.0;
        double DirY = Distance2D > 0.0 ? DeltaY / Distance2D : 0.0;

        FVector Target;

        if (bIsVehicle)
        {
            FCall VehicleVelocity(HitActor, "K2_GetActorVelocity");
            FVector VehicleVel;

            if (VehicleVelocity.Ok())
            {
                VehicleVelocity.Call();
                VehicleVel = VehicleVelocity.GetVector("ReturnValue");
            }

            auto VehicleName = HitActor->Name.ToString();

            if (Contains(VehicleName, "Antelope") || Contains(VehicleName, "Meatball") || Contains(VehicleName, "Winter"))
            {
                Target = FVector(VehicleVel.X * 4.0, VehicleVel.Y * 4.0, 25000.0);
                PumpkinProjectile::Log("ProcessEvent", "super launch triggered by %s", VehicleName.c_str());
            }
            else
            {
                double DoubleSpeed = VehicleVel.Magnitude() * 2.0;

                if (DoubleSpeed < 1000.0)
                    DoubleSpeed = 1000.0;

                Target = FVector(VehicleVel.X * 2.0, VehicleVel.Y * 2.0, DoubleSpeed);
            }
        }
        else
        {
            double LookDown = 0.0;

            if (PlayerPitch < 0.0)
                LookDown = (std::min)(1.0, (PlayerPitch * -1.0) / 90.0);

            double BaseHorizontal = 7000.0 - (17000.0 * LookDown);
            double BaseVertical = 5500.0 + (11000.0 * LookDown);
            double Horizontal = (std::max)(500.0, BaseHorizontal + (double)((rand() % 4001) - 1000));
            double Vertical = (std::max)(500.0, BaseVertical + (double)((rand() % 4001) - 1000));
            Target = FVector(DirX * Horizontal, DirY * Horizontal, Vertical);
        }

        if (Instigator)
        {
            double ZDiff = InstigatorLocation.Z - CompLocation.Z;
            double Distance3D = std::sqrt(DeltaX * DeltaX + DeltaY * DeltaY + ZDiff * ZDiff);
            bool bHitRocket = Contains(HitActor->Name.ToString(), "B_Prj_Ranged_Rocket_Athena");

            if (bHitRocket && Distance3D <= 300.0)
                LaunchCharacter(Instigator, DirX * 10000.0, DirY * 10000.0, 8000.0);
            else if (Distance2D < 500.0 && ZDiff > -300.0 && ZDiff < 600.0)
                LaunchCharacter(Instigator, Target.X, Target.Y, Target.Z);
        }

        FCall Impulse(HitComp, "AddImpulse");

        if (Impulse.Ok())
        {
            FCall Mass(HitComp, "GetMass");
            double ComponentMass = 1000.0;

            if (Mass.Ok())
            {
                Mass.Call();
                float Value = Mass.Get<float>("ReturnValue");
                ComponentMass = Value < 1.f ? 1000.0 : (double)Value;
            }

            Impulse.SetVector("Impulse", FVector(Target.X * ComponentMass * 2.5, Target.Y * ComponentMass * 2.5, Target.Z * ComponentMass * 2.5));
            Impulse.Set("bVelocityChange", false);
            Impulse.Call();
        }
    }

    void HandleUmbrellaBounce(UObject* Object, UFunction* Function, void* Params)
    {
        auto MovementComponent = GetComponentByClass(Object, FindClass("ProjectileMovementComponent"));

        if (!MovementComponent)
            return;

        auto VelocityOffset = GetObjectOffset(MovementComponent, "Velocity");

        if (VelocityOffset == (uint32)-1)
            return;

        auto& Velocity = *(FVector*)(__int64(MovementComponent) + VelocityOffset);
        FVector Normal = ReadVectorParam(Function, Params, "HitNormal");
        double Dot = Velocity.X * Normal.X + Velocity.Y * Normal.Y + Velocity.Z * Normal.Z;

        FVector Reflected((Velocity.X - 2.0 * Dot * Normal.X) * 2.0, (Velocity.Y - 2.0 * Dot * Normal.Y) * 2.0, (Velocity.Z - 2.0 * Dot * Normal.Z) * 2.0);
        Velocity.X = Reflected.X;
        Velocity.Y = Reflected.Y;
        Velocity.Z = Reflected.Z;

        SetProp<float>(MovementComponent, "Bounciness", 2.f);
        SetProp<float>(MovementComponent, "Friction", 0.f);
        SetProp<float>(MovementComponent, "BounceVelocityStopSimulatingThreshold", 5.f);
    }

    void HandleHit(UObject* Object, UFunction* Function, void* Params, const FClassInfo& Info)
    {
        FVector HitLocation = ReadVectorParam(Function, Params, "HitLocation");
        auto Other = ReadParam<UObject*>(Function, Params, "Other");
        auto OtherComp = ReadParam<UObject*>(Function, Params, "OtherComp");

        if (Info.bTowerGrenade && HitLocation.X != 0.0)
            HandleTowerGrenadeHit(Object, HitLocation);

        if (!Other)
            return;

        auto OtherName = Other->Name.ToString();

        if (Info.bOffRoadTire && OtherComp)
            HandleOffRoadTireHit(Object, Other, OtherComp, Info);

        if (Contains(OtherName, "Umbrella") || Contains(OtherName, "umbrella") || Contains(OtherName, "Brolly") || Contains(OtherName, "brolly"))
            HandleUmbrellaBounce(Object, Function, Params);
    }

    void HandleOverlap(UObject* Object, UFunction* Function, void* Params)
    {
        auto OtherActor = ReadParam<UObject*>(Function, Params, "OtherActor");

        if (!OtherActor)
            return;

        auto OtherName = OtherActor->Name.ToString();

        if (!Contains(OtherName, "Umbrella") && !Contains(OtherName, "umbrella") && !Contains(OtherName, "Brolly") && !Contains(OtherName, "brolly"))
            return;

        SetCollisionResponseAll(GetProp<UObject*>(Object, "RootComponent"), 2);
        SetCollisionResponseAll(GetProp<UObject*>(OtherActor, "RootComponent"), 2);
    }

    // ------------------------------------------------------------------
    // Deferred-spawn support (replaces UWorld::SpawnActor from the old SDK wrapper)
    // ------------------------------------------------------------------

    struct FRot
    {
        double Pitch = 0.0;
        double Yaw = 0.0;
        double Roll = 0.0;
    };

    bool ReadRotator(const FCall& Call, const char* Param, FRot& Out)
    {
        if (!Call.Ok())
            return false;

        auto Offset = GetStructOffset((const UStruct*)Call.Fn, Param);

        if (Offset == (uint32)-1)
            return false;

        const uint8* Data = Call.Buf + Offset;

        if (IsLWC())
        {
            double Values[3];
            memcpy(Values, Data, sizeof(Values));
            Out.Pitch = Values[0];
            Out.Yaw = Values[1];
            Out.Roll = Values[2];
        }
        else
        {
            float Values[3];
            memcpy(Values, Data, sizeof(Values));
            Out.Pitch = Values[0];
            Out.Yaw = Values[1];
            Out.Roll = Values[2];
        }

        return true;
    }

    // Builds a raw FTransform (quat, translation, scale) in the layout of the running engine version.
    size_t BuildTransform(uint8* Out, const FVector& Location, const FRot& Rotation, double Scale)
    {
        const double ToHalfRad = 0.00872664625;
        double SP = std::sin(Rotation.Pitch * ToHalfRad), CP = std::cos(Rotation.Pitch * ToHalfRad);
        double SY = std::sin(Rotation.Yaw * ToHalfRad), CY = std::cos(Rotation.Yaw * ToHalfRad);
        double SR = std::sin(Rotation.Roll * ToHalfRad), CR = std::cos(Rotation.Roll * ToHalfRad);

        double Quat[4] = { CR * SP * SY - SR * CP * CY, -CR * SP * CY - SR * CP * SY, CR * CP * SY - SR * SP * CY, CR * CP * CY + SR * SP * SY };

        if (IsLWC())
        {
            double Translation[3] = { (double)Location.X, (double)Location.Y, (double)Location.Z };
            double ScaleVec[3] = { Scale, Scale, Scale };
            memset(Out, 0, 96);
            memcpy(Out + 0, Quat, sizeof(Quat));
            memcpy(Out + 32, Translation, sizeof(Translation));
            memcpy(Out + 64, ScaleVec, sizeof(ScaleVec));
            return 96;
        }

        float QuatF[4] = { (float)Quat[0], (float)Quat[1], (float)Quat[2], (float)Quat[3] };
        float TranslationF[3] = { (float)Location.X, (float)Location.Y, (float)Location.Z };
        float ScaleF[3] = { (float)Scale, (float)Scale, (float)Scale };
        memset(Out, 0, 48);
        memcpy(Out + 0, QuatF, sizeof(QuatF));
        memcpy(Out + 16, TranslationF, sizeof(TranslationF));
        memcpy(Out + 32, ScaleF, sizeof(ScaleF));
        return 48;
    }

    UObject* GetGameplayStatics()
    {
        static UObject* Default = nullptr;

        if (!Default)
        {
            // Not GetDefaultObj(): in this SDK that is a static that returns the default object of UClass itself.
            auto Class = UGameplayStatics::StaticClass();
            Default = Class ? Class->ClassDefaultObject : nullptr;

            if (Default)
                PumpkinProjectile::Log("ProcessEvent", "GameplayStatics default object %s (class %s)", Default->Name.ToString().c_str(), Default->Class ? Default->Class->Name.ToString().c_str() : "null");
        }

        return Default;
    }

    UObject* FindWorld(UObject* Object)
    {
        FCall WorldCall(Object, "K2_GetWorld");

        if (WorldCall.Ok())
        {
            WorldCall.Call();

            if (auto World = WorldCall.Get<UObject*>("ReturnValue"))
                return World;
        }

        static const UClass* WorldClass = FindClass("World");

        for (auto Outer = Object ? Object->Outer : nullptr; Outer; Outer = Outer->Outer)
            if (WorldClass && Outer->IsA(WorldClass))
                return Outer;

        return nullptr;
    }

    // Diagnostic: logs the full path of every loaded object whose name contains Part.
    void LogObjectsNamed(const char* Part)
    {
        int32 Found = 0;

        for (int32 i = 0; i < UObject::GObjects->Num() && Found < 20; i++)
        {
            auto Obj = UObject::GObjects->GetByIndex(i);

            if (!Obj)
                continue;

            auto Name = Obj->Name.ToString();

            if (!Contains(Name, Part))
                continue;

            std::string Path = Name;

            for (auto Outer = Obj->Outer; Outer; Outer = Outer->Outer)
                Path = Outer->Name.ToString() + "." + Path;

            PumpkinProjectile::Log("ProcessEvent", "loaded object matching '%s': %s (class %s)", Part, Path.c_str(), Obj->Class ? Obj->Class->Name.ToString().c_str() : "null");
            Found++;
        }

        if (!Found)
            PumpkinProjectile::Log("ProcessEvent", "no loaded object matching '%s'", Part);
    }

    void HandleProjectileReady(UObject* Object, const FClassInfo& Info)
    {
        // Looked up on every call until found: a class that isn't loaded yet must not be cached as null.
        static const UClass* RocketClass = nullptr;
        static const UClass* PumpkinClass = nullptr;

        if (!RocketClass)
            RocketClass = FindClass("B_Prj_Ranged_Rocket_Athena_C");

        if (!PumpkinClass)
            PumpkinClass = FindClass("B_Prj_Ranged_PumpkinRocket_Athena_C");

        auto Skip = [&](const char* Why)
            {
                static int32 SkipLogged = 0;

                if (SkipLogged++ < 60)
                    PumpkinProjectile::Log("ProcessEvent", "projectile %s (%s) not replaced: %s", Object->Name.ToString().c_str(), Info.Name.c_str(), Why);
            };

        auto TargetClass = Info.bHookBoss ? RocketClass : PumpkinClass;

        if (!TargetClass)
        {
            static int32 Scans = 0;
            static ULONGLONG LastScan = 0;
            ULONGLONG Now = GetTickCount64();

            if (Scans < 3 && Now - LastScan > 10000)
            {
                Scans++;
                LastScan = Now;
                LogObjectsNamed(Info.bHookBoss ? "Rocket_Athena" : "PumpkinRocket");
            }
        }

        if (!TargetClass)
            return Skip(Info.bHookBoss ? "FindClass(B_Prj_Ranged_Rocket_Athena_C) returned null" : "FindClass(B_Prj_Ranged_PumpkinRocket_Athena_C) returned null");

        auto Root = GetProp<UObject*>(Object, "RootComponent");

        if (!Root)
            return Skip("no RootComponent");

        auto World = FindWorld(Object);
        auto Statics = GetGameplayStatics();

        if (!World)
            return Skip("FindWorld returned null");

        if (!Statics)
            return Skip("GameplayStatics default object not found");

        auto Instigator = GetProp<UObject*>(Object, "Instigator");
        auto Owner = GetProp<UObject*>(Object, "Owner");

        FVector Location;
        FCall LocationCall(Object, "K2_GetActorLocation");

        if (LocationCall.Ok())
        {
            LocationCall.Call();
            Location = LocationCall.GetVector("ReturnValue");
        }

        FRot Rotation;
        FCall RotationCall(Object, "K2_GetActorRotation");

        if (RotationCall.Ok())
        {
            RotationCall.Call();
            ReadRotator(RotationCall, "ReturnValue", Rotation);
        }

        auto OriginalMovement = GetComponentByClass(Object, FindClass("ProjectileMovementComponent"));
        FVector Velocity;
        float Speed = 0.f;

        if (OriginalMovement)
        {
            Velocity = GetProp<FVector>(OriginalMovement, "Velocity");
            Speed = (float)Velocity.Magnitude();

            if (Speed < 10.f)
                Speed = GetProp<float>(OriginalMovement, "InitialSpeed");
        }

        if (Speed < 10.f)
            Speed = 3000.f;

        // Rotation and the 2.5x scale go in through the spawn transform.
        uint8 Transform[128] = {};
        size_t TransformSize = BuildTransform(Transform, Location, Rotation, 2.5);

        FCall Begin(Statics, "BeginDeferredActorSpawnFromClass");

        if (!Begin.Ok())
        {
            PumpkinProjectile::Log("ProcessEvent", "BeginDeferredActorSpawnFromClass not found");

            static bool bListed = false;

            if (!bListed)
            {
                bListed = true;

                auto StaticsClass = Statics->Class;
                auto Found = StaticsClass ? StaticsClass->FindFunction("BeginDeferredActorSpawnFromClass") : nullptr;

                PumpkinProjectile::Log("ProcessEvent", "statics class %s, FindFunction %s, params size %d (buffer %d)", StaticsClass ? StaticsClass->Name.ToString().c_str() : "null", Found ? "found" : "NULL",
                    Found ? (int)((const UStruct*)Found)->Size : -1, (int)sizeof(Begin.Buf));

                for (int32 i = 0; i < UObject::GObjects->Num(); i++)
                {
                    auto Obj = UObject::GObjects->GetByIndex(i);

                    if (!Obj || Obj->Outer != StaticsClass)
                        continue;

                    auto FnName = Obj->Name.ToString();

                    if (Contains(FnName, "Spawn"))
                        PumpkinProjectile::Log("ProcessEvent", "GameplayStatics function: %s", FnName.c_str());
                }
            }

            return;
        }

        Begin.Set("WorldContextObject", World);
        Begin.Set("ActorClass", TargetClass);
        Begin.SetRaw("SpawnTransform", Transform, TransformSize);
        Begin.Set<uint8>("CollisionHandlingOverride", 1);
        Begin.Set("Owner", Owner);
        Begin.Call();

        auto Spawned = Begin.Get<UObject*>("ReturnValue");

        if (!Spawned)
        {
            PumpkinProjectile::Log("ProcessEvent", "deferred spawn failed for %s", Object->Name.ToString().c_str());
            return;
        }

        SetProp<UObject*>(Spawned, "Instigator", Instigator);
        SetProp<UObject*>(Spawned, "Owner", Owner);

        FCall Finish(Statics, "FinishSpawningActor");

        if (Finish.Ok())
        {
            Finish.Set("Actor", Spawned);
            Finish.SetRaw("SpawnTransform", Transform, TransformSize);
            Finish.Call();
        }

        auto SpawnedRoot = GetProp<UObject*>(Spawned, "RootComponent");
        SetCollisionResponseAll(SpawnedRoot, 2);

        if (SpawnedRoot)
        {
            FCall Ccd(SpawnedRoot, "SetUseCCD");
            Ccd.Set("bInUseCCD", true);
            Ccd.Call();
        }

        auto SpawnedMovement = GetComponentByClass(Spawned, FindClass("ProjectileMovementComponent"));

        if (SpawnedMovement)
        {
            SetProp<float>(SpawnedMovement, "InitialSpeed", Speed);
            SetProp<float>(SpawnedMovement, "MaxSpeed", (std::max)(Speed, GetProp<float>(SpawnedMovement, "MaxSpeed")));

            auto VelocityOffset = GetObjectOffset(SpawnedMovement, "Velocity");

            if (VelocityOffset != (uint32)-1 && OriginalMovement)
                memcpy((void*)(__int64(SpawnedMovement) + VelocityOffset), &Velocity, sizeof(FVector));

            if (OriginalMovement)
            {
                SetProp<float>(SpawnedMovement, "ProjectileGravityScale", GetProp<float>(OriginalMovement, "ProjectileGravityScale"));
                SetProp<float>(SpawnedMovement, "Bounciness", GetProp<float>(OriginalMovement, "Bounciness"));
                SetProp<float>(SpawnedMovement, "Friction", GetProp<float>(OriginalMovement, "Friction"));
            }
        }

        auto RotatingComponent = GetComponentByClass(Spawned, FindClass("RotatingMovementComponent"));

        if (RotatingComponent)
        {
            FCall Deactivate(RotatingComponent, "Deactivate");
            Deactivate.Call();
        }

        if (TargetClass == PumpkinClass)
        {
            if (SpawnedMovement)
            {
                FCall Deactivate(SpawnedMovement, "Deactivate");
                Deactivate.Call();
            }

            FCall Attach(Spawned, "K2_AttachToActor");

            if (Attach.Ok())
            {
                Attach.Set("ParentActor", Object);
                Attach.Set<uint8>("LocationRule", 2);
                Attach.Set<uint8>("RotationRule", 2);
                Attach.Set<uint8>("ScaleRule", 0);
                Attach.Set("bWeldSimulatedBodies", false);
                Attach.Call();
            }

            FCall Hide(Root, "SetVisibility");
            Hide.Set("bNewVisibility", false);
            Hide.Set("bPropagateToChildren", true);
            Hide.Call();
        }

        FCall EnableCollision(Spawned, "SetActorEnableCollision");
        EnableCollision.Set("bNewActorEnableCollision", true);
        EnableCollision.Call();

        static int32 Logged = 0;

        if (Logged++ < 40)
            PumpkinProjectile::Log("ProcessEvent", "replaced projectile %s with %s speed=%.0f", Object->Name.ToString().c_str(), TargetClass->Name.ToString().c_str(), (double)Speed);
    }

    void RunHandlers(UObject* Object, UFunction* Function, void* Params, const FFnInfo& Fn, const FClassInfo& Info)
    {
        if (Info.bFireMesh && Info.bActor)
            HandleFireMesh(Object);

        if (!FireActorsToDestroy.empty())
            FlushFireMeshes();

        if ((Fn.Flags & FnScan) && Info.bActor)
            ScanUmbrella(Object);

        if ((Fn.Flags & FnCharTick) && Info.bCharacter)
            UpdateCharacterVelocity(Object);

        if (Fn.Flags & FnJumpCollision)
        {
            HandleJumpCollision(Function, Params);
            return;
        }

        if (!Info.bProjectile)
            return;

        if (Fn.Flags & FnHit)
            HandleHit(Object, Function, Params, Info);
        else if (Fn.Flags & FnOverlap)
            HandleOverlap(Object, Function, Params);
        else if ((Fn.Flags & FnReady) && !Info.bSkipReplace)
            HandleProjectileReady(Object, Info);
    }

    void ProcessEventHook(UObject* Object, UFunction* Function, void* Params)
    {
        ProcessEventOG(Object, Function, Params);

        if (bInHandler || !Object || !Function || !Object->Class)
            return;

        bInHandler = true;

        {
            std::lock_guard<std::mutex> Lock(CacheMutex);
            auto& Fn = GetFnInfo(Object, Function);
            auto& Info = GetClassInfo(Object);

            DumpTop();

            if (Fn.Flags || Info.bFireMesh || !FireActorsToDestroy.empty())
                RunHandlers(Object, Function, Params, Fn, Info);
        }

        bInHandler = false;
    }
}

void PumpkinProjectile::Log(const char* Module, const char* Fmt, ...)
{
    static FILE* File = nullptr;

    if (!File)
    {
        char Path[MAX_PATH] = {};
        GetModuleFileNameA(nullptr, Path, MAX_PATH);
        auto Slash = strrchr(Path, '\\');

        if (Slash)
            Slash[1] = 0;

        strcat_s(Path, "PumpkinProjectile_log.txt");
        fopen_s(&File, Path, "w");
    }

    if (!File)
        return;

    fprintf(File, "[%s] ", Module);
    va_list Args;
    va_start(Args, Fmt);
    vfprintf(File, Fmt, Args);
    va_end(Args);
    fprintf(File, "\n");
    fflush(File);
}

void PumpkinProjectile::Install()
{
    Log("ProcessEvent", "Install called");

    uintptr_t Address = ImageBase + ProcessEventRva;
    auto DefaultObject = UObject::StaticClass() ? UObject::StaticClass()->GetDefaultObj() : nullptr;

    if (DefaultObject && (uintptr_t)DefaultObject->VTable[ProcessEventVft] != Address)
        Log("ProcessEvent", "vtable slot 0x%llx holds 0x%llx, not the 32.11 address 0x%llx: using the vtable", (unsigned long long)ProcessEventVft,
            (unsigned long long)((uintptr_t)DefaultObject->VTable[ProcessEventVft] - ImageBase), (unsigned long long)ProcessEventRva);

    if (DefaultObject)
        Address = (uintptr_t)DefaultObject->VTable[ProcessEventVft];

    bool bHooked = Hook(Address, ProcessEventHook, ProcessEventOG);
    Log("ProcessEvent", "hook %s at 0x%llx (vtable slot 0x%llx)", bHooked ? "installed" : "FAILED", (unsigned long long)(Address - ImageBase), (unsigned long long)ProcessEventVft);
}
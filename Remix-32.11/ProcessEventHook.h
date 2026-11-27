#pragma once

#include <cstdint>

namespace PumpkinProjectile
{
    constexpr uintptr_t ProcessEventRva = 0x1655C14;
    constexpr uintptr_t ProcessEventVft = 0x46;
    inline bool bProjectilePumpkinReplace = true;
    inline float ProjectileCollisionScale = 2.5f;

    void Log(const char* Module, const char* Fmt, ...);
    void Install();
}
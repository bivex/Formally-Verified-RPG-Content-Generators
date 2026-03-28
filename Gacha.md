# Gacha Engine — Formal Model Reference

> All numbers are formally verified in Dafny 4.11. Every table below maps directly to a lemma or `ensures` clause in `src/`.

---

## Module Dependency Tree

```
Characters.dfy          ← root: Element × WeaponType × StarRarity
│
├── Weapons.dfy         ← adds Substat × Refinement
│   ├── Banners.dfy     ← banner configs (BannerType × featured slot)
│   ├── Pity.dfy        ← pity state machine + 6 lemmas
│   ├── Economy.dfy     ← pull packages, primo costs
│   ├── Pulls.dfy       ← pull scenarios
│   ├── Rarest100.dfy   ← top-100 hardest-to-obtain items
│   └── GachaStats.dfy  ← grand totals, dimension proofs
│
└── GachaStats.dfy
```

---

## Combinatorial Space

| Module | Dim 1 | Dim 2 | Dim 3 | Dim 4 | **Total** |
| :----- | :---: | :---: | :---: | :---: | --------: |
| `Characters.dfy` | 7 elements | 5 weapon types | 3 rarities | — | **105** |
| `Weapons.dfy` | 5 types | 3 rarities | 7 substats | 5 refs | **525** |
| `Banners.dfy` | 3 banner types | 7 elements | 5 weapon types | — | **105** |
| `Pity.dfy` — states | 91 (since5★: 0‥90) | 11 (since4★: 0‥10) | 2 (guaranteed: T/F) | — | **2 002** |
| `Economy.dfy` | 180 packages (1‥180) | — | — | — | **180** |
| `Pulls.dfy` — scenarios | 91 (pity counter) | 2 (at hard pity / not) | — | — | **182** |
| | | | | **GRAND TOTAL** | **3 099** |

Proved in `GachaStats.TotalsAreCorrect()`.

---

## Banner Pull Rates

| Banner | 5★ base rate | 4★ base rate | 3★ rate | Hard pity | Soft pity starts | 50/50 | Epitomized path |
| :----- | -----------: | -----------: | ------: | --------: | :--------------: | :---: | :-------------: |
| **Character** | 0.60 % | 5.10 % | 94.30 % | 90 | pull 74 | Yes | No |
| **Weapon** | 0.70 % | 6.00 % | 93.30 % | 80 | pull 62 | No | Yes (2nd copy) |
| **Standard** | 0.60 % | 5.10 % | 94.30 % | 90 | pull 74 | No | No |

Constants live in `Banners.dfy`: `RATE_5STAR_CHAR`, `HARD_PITY_CHAR`, `SOFT_PITY_WEAPON`, …

---

## Pity State Machine

```
PityState = { since5Star: 0‥90, since4Star: 0‥10, guaranteed: bool, totalPulls: nat }

Pull outcome        │ Trigger condition (proved by lemma)
────────────────────┼──────────────────────────────────────────────────
Got5Star(featured)  │ HardPityForcesR5:   since5Star == 90  → must 5★
                    │ GuaranteeHolds:     guaranteed == true → must featured
Got4Star            │ HardPity4ForcesR4:  since4Star == 10   → must 4★ or 5★
Got3Star            │ any other pull
────────────────────┼──────────────────────────────────────────────────
After 5★ (featured) │ FeaturedR5ClearsGuarantee: guaranteed → false
After 5★ (lost)     │ StandardR5SetsGuarantee:   guaranteed → true
After 5★ (any)      │ R5ResetsBothCounters:       since5Star, since4Star → 0
```

6 lemmas in `Pity.dfy`, all verified with 0 errors.

---

## Worst-Case Pull Cost (Weapon Banner, Epitomized Path)

```
1 copy  =  HARD_PITY_WEAPON × EPITOMIZED_FACTOR  =  80 × 2  =  160 pulls
R5 cost =  refinement × 160 pulls
        =  refinement × 160 × 160 primogems
```

| Refinement | Pulls (worst case) | Primogems (worst case) | Monthly F2P time* |
| :--------: | -----------------: | ---------------------: | ----------------: |
| R1 | 160 | 25 600 | ~10 months |
| R2 | 320 | 51 200 | ~20 months |
| R3 | 480 | 76 800 | ~30 months |
| R4 | 640 | 102 400 | ~39 months |
| R5 | 800 | 128 000 | ~49 months |

*F2P baseline: `F2P_PRIMOS_MONTHLY = 2 600` primos/month (`Economy.dfy`).
Proved in `Rarest100.WorstCasePrimos()`.

---

## Difficulty Score Model (Rarest100)

```
Score(ref, substat) = ref × 1000 + SubstatPriority(substat) × 10
```

Refinement gap (1 000) always dominates substat gap (max 70), proved by `HigherRefDominates`.

### Substat Priority

| Priority | Substat | Why it matters |
| :------: | :------ | :------------- |
| 7 | CritDMG | Highest DPS multiplier |
| 6 | CritRate | Enables CritDMG to trigger |
| 5 | ATK% | Scales all damage output |
| 4 | Energy Recharge | Enables burst rotation |
| 3 | Elem Mastery | Strong for reaction builds |
| 2 | HP% | Survivability / some HP-scaling |
| 1 | DEF% | Weakest damage-to-stat ratio |

### Score Ranges by Tier

| Rank band | Refinement | Score range | Example |
| :-------- | :--------: | :---------: | :------ |
| 1–35 | ref = 5 | 5 010 – 5 070 | *Calamity's Fang, the Unrivaled* |
| 36–70 | ref = 4 | 4 010 – 4 070 | *Calamity's Fang, the Ascendant* |
| 71–100 | ref = 3 | 3 020 – 3 070 | *Calamity's Fang Reforged* |

Tier 3 excludes DEF% (priority 1) — only top-6 substats qualify.

---

## AAA Weapon Naming System

Each name is fully determined by `(WeaponType, StarRarity, Substat, Refinement)`.
No randomness — every combination always produces the same name.

### Vocabulary by Tier

| Substat | R5 — Mythic word | R4 — Heroic adjective | R3 — Earth material |
| :------ | :--------------: | :-------------------: | :-----------------: |
| CritDMG | **Calamity** | Ruinous | Obsidian |
| CritRate | **Havoc** | Tempest | Flint |
| ATK% | **Conquest** | Sovereign | Iron |
| Elem Mastery | **Aether** | Esoteric | Jade |
| Energy Recharge | **Eternity** | Flowing | Quartz |
| HP% | **Bastion** | Ironclad | Timber |
| DEF% | **Aegis** | Rampart | Granite |

| WeaponType | R5 — Mythic noun | R4 — Heroic noun | R3 — Common noun |
| :--------- | :--------------: | :--------------: | :--------------: |
| Sword | **Fang** | Blade | Sword |
| Catalyst | **Grimoire** | Codex | Tome |
| Polearm | **Spire** | Halberd | Spear |
| Claymore | **Colossus** | Crusher | Greatsword |
| Bow | **Harbinger** | Stringer | Bow |

### Refinement Progression

| Refinement | R5 epithet | R4 mark | R3 mark |
| :--------: | :--------- | :------ | :------ |
| R1 | *(base name)* | *(base name)* | *(base name)* |
| R2 | … Reborn | …+ | … +1 |
| R3 | … Reforged | …++ | … +2 |
| R4 | …, the Ascendant | …+++ | … +3 |
| R5 | **…, the Unrivaled** | … [MAX] | … +4 |

### Full Name Formula

```
R5 →  [SubstatMythic]'s [WeaponNounMythic][R5Epithet]
        "Calamity's Fang, the Unrivaled"    (CritDMG · Sword · ref=5)
        "Eternity's Grimoire Reforged"       (ER · Catalyst · ref=3)
        "Havoc's Harbinger"                  (CritRate · Bow · ref=1)

R4 →  [SubstatHeroic] [WeaponNounHeroic][R4Mark]
        "Ruinous Blade+++"                   (CritDMG · Sword · ref=4)
        "Flowing Codex"                      (ER · Catalyst · ref=1)

R3 →  [SubstatMaterial] [WeaponNounCommon][R3Mark]
        "Obsidian Sword +2"                  (CritDMG · Sword · ref=3)
        "Jade Tome"                          (EM · Catalyst · ref=1)
```

---

## Running the Engine

```bash
# Verify all gacha modules (0 errors expected)
dafny verify src/Characters.dfy src/Weapons.dfy src/Banners.dfy \
             src/Pity.dfy src/Economy.dfy src/Pulls.dfy src/GachaStats.dfy

# Generate top-100 rarest items
dafny run --main-method Rarest100.MainRarest100 src/Rarest100.dfy \
  2>/dev/null > output/rarest100.txt

# Formal audit (0 findings expected)
./scripts/audit_dafny.sh
```

---

*Formally verified. Mathematically balanced. Ready to ship.*

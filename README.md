# 🔮 Formally Verified RPG Content Engine (Dafny 4.11)

> **"In code we trust, but in Math we verify."**  
> A high-performance, mathematically proven procedural generation ecosystem for RPGs. Every item, monster, and quest is guaranteed to be balanced, deterministic, and free from logical paradoxes.

---

## 🏗️ The Multi-Genre Architecture
This engine is built on **Generic Logic Patterns**. While the default "Skin" is High Fantasy, the core mathematical invariants are **Genre-Agnostic**. 

| System | Fantasy Skin (Default) | Sci-Fi Skin | Cyberpunk Skin |
| :--- | :--- | :--- | :--- |
| **MagicItems** | `Sword of Inferno` | `Plasma Cutter` | `Neural Monoblade` |
| **Locations** | `Volcano Dungeon` | `Ion Storm Nebula` | `MegaCorp Server Farm` |
| **Monsters** | `Ancient Red Dragon` | `Xeno-Hive Queen` | `Rogue AI Sentinel` |
| **Spells** | `Fireball (Evocation)` | `Thermal Burst` | `System Overload (Logic)` |

---

## 🗃️ Core Modules (Proven & Validated)

Every module in `src/` is built with a `Valid()` predicate and follows the **Strict Audit Protocol**.

*   ⚔️ **`Combat.dfy`**: The heart of the simulation. A deterministic battle engine where mana management and turn resolution are formally proven.
*   📜 **`Quests.dfy`**: (New!) Mission generator connecting NPCs, Locations, and rewards. Proves that high-risk objectives always yield high-value rewards.
*   ⚖️ **`Balancer.dfy`**: The "Global Auditor". A meta-module that proves social and economic hierarchies hold TRUE across the entire universe.
*   🗡️ **`MagicItems.dfy` & `Spells.dfy`**: Generators for billions of balanced artifacts and abilities.
*   🏰 **`Locations.dfy`**: Procedural world generator with biome-specific danger scaling.
*   🧙‍♂️ **`NPCs.dfy`**: Social entity generator with verified class-based economic traits.

---

## 🛠️ Professional Toolchain

We provide automation scripts for continuous integration and stability:

*   **`scripts/audit_dafny.sh`**  
  Performs a strict formal audit (determinism, shadowing, print-effects) across the codebase.
*   **`scripts/check_metrics.sh`**  
  A visual complexity analyzer. Highlights any method that consumes excessive verification resources to prevent timeouts.

---

## 💻 How to Run & Generate

### 1. Verification & Generation
To generate fresh binary-data databases in the `output/` folder:

```bash
# Generate all databases
# Each module has a named entry point, so --main-method is required
dafny run --main-method MagicItems.MainMagicItems src/MagicItems.dfy 2>/dev/null > output/magic_items.txt
dafny run --main-method Locations.MainLocations   src/Locations.dfy  2>/dev/null > output/locations.txt
dafny run --main-method Monsters.MainMonsters     src/Monsters.dfy   2>/dev/null > output/monsters.txt
dafny run --main-method NPCs.MainNPCs             src/NPCs.dfy       2>/dev/null > output/npcs.txt
dafny run --main-method Spells.MainSpells         src/Spells.dfy     2>/dev/null > output/spells.txt
dafny run --main-method Combat.MainCombat         src/Combat.dfy     2>/dev/null > output/combat.txt
dafny run --main-method Quests.MainQuests         src/Quests.dfy     2>/dev/null > output/quests.txt
```

### 2. Formal Audit
To ensure the world is still balanced after your changes:
```bash
./scripts/audit_dafny.sh
```

---

## 🚧 Status & Roadmap

| Feature | Status | Description |
| :--- | :---: | :--- |
| **Procedural Generation** | ✅ | Done for Items, Monsters, NPCs, Spells, Locations. |
| **Formal Balance** | ✅ | Cross-module lemmas prove social/combat hierarchies. |
| **Core Loop** | ✅ | Battle engine and Turn-resolution proven. |
| **Quest System** | ⏳ | Advanced multi-step chains (Initial Tier implemented). |
| **Reputation System** | 📅 | *Planned*: Mutual exclusivity of faction standing. |
| **Persistence Layer** | 📅 | *Planned*: Formal JSON serialization to disk. |

---

## 🛡️ Why Formal Verification?
In modern game development, balancing an MMO or a large RPG manually is impossible. One small change to a multiplier can break the economy. **Dafny** allows us to:
1.  **Eliminate Edge-case Bugs**: No more division-by-zero or negative HP.
2.  **Guaranteed Fairness**: Mathematical proofs that a legendary item is always better than a common one.
3.  **Instant Feedback**: The compiler tells the designer if they broke the game *before* it's even compiled.

---
**Architected with Precision. Verified by Logic.**

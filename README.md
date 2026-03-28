# Formally Verified RPG Content Generators

Welcome to the **Formally Verified RPG Content Generators** repository. This project demonstrates the power of formal methods and rigorous theorem proving applied to procedural generation for RPG games. 

Instead of writing standard unverified scripts that might produce invalid item combinations or bugs, this repository uses **[Dafny](https://github.com/dafny-lang/dafny)** — a verification-aware programming language — to mathematically prove the correctness of all generated content.

## 🚀 Features

* **Mathematical Guarantees**: Every procedural generator acts as a formal spec. Dafny proves at *compile time* that generated locations or items will never violate their internal logic rules.
* **Complex Data Modeling**: Exhaustive `datatype` definitions (enums) mapping specific biome sizes and magical types to specific behaviors.
* **Zero Overhead "Dead Code" & Unsoundness**: The code is fully audited against logical fallacies or dirty assertions (e.g., `assume`).
* **Optimized Verification**: Generators are refactored to limit logical branching and sequences, reducing verifier resource burden significantly (under 1 million resources per task).

## 🗃️ Codebase Structure

The project currently contains two main procedural generators:

1. **`MagicItems.dfy`** - Generates unique magical weapons and artifacts based on Element, Type, and Rarity. Calculates power levels with balancing rules verified by Dafny.
2. **`Locations.dfy`** - Generates unique names and danger levels for RPG locations (dungeons, cities, ruins) based on Biome, Size, and Location Type.

## 🛠️ Tools & Scripts

We have custom automation scripts built to easily run audits and verify complexity bounds across all `.dfy` files:

* **`audit_dafny.sh`**  
  A one-click formal audit runner that strictly enforces:
  - Determinism rules (`--enforce-determinism`)
  - No missing constructor parentheses
  - Strict tracking of impure printing methods (`--track-print-effects`)
  - Absence of logical errors/unsoundness (`dafny audit`)

  *Usage:* `./audit_dafny.sh` (audits all) or `./audit_dafny.sh Locations.dfy`

* **`check_metrics.sh`**  
  A beautiful colored complexity analyzer. Scans `.dfy` verification trace outputs and highlights any logic that is taking too many resources (`Heavy Tasks`) to verify. This actively protects the developer from "verification timeouts".

  *Usage:* `./check_metrics.sh`

## 💻 How to Run

Since the Dafny code is formally verified and correct, you can confidently run it via the terminal directly or compile to target languages:

```bash
# Run the magic items procedural generator directly
dafny run MagicItems.dfy

# Run the locations procedural generator directly
dafny run Locations.dfy
```

*(You can also compile it to C#, Go, Java, C++, JS or Python using the `dafny build` command!)*

## 🗺️ Matrix Features for Games

To build a complete, formally verified procedural RPG, we need multiple interconnected systems. Here is the current Ecosystem Matrix representing our generator coverage:

| Feature Generator | Status | Description | Formal Verification Goal |
| :--- | :---: | :--- | :--- |
| 🛡️ **Items & Loot** (`MagicItems.dfy`) | ✅ | Weapons, artifacts, elements, rarity scaling | Prove power balance formulas and elemental synergy. |
| 🏰 **World & Locations** (`Locations.dfy`) | ✅ | Biomes, dungeons, cities, danger calculation | Prove danger levels correlate strictly with size/biome. |
| 🧙‍♂️ **NPCs & Characters** (`NPCs.dfy`) | ✅ | Names, races, classes, alignments, professions | Prove stat distributions and logical origin traits. |
| 🐉 **Monsters & Encounters** (`Monsters.dfy`) | ✅ | Creature types, abilities, HP/Damage scaling | Prove mathematical fairness of combat stats vs player levels. |
| ✨ **Spells & Abilities** (`Spells.dfy`) | ✅ | Magic schools, mana costs, cooldowns, pure logic | Prove spell costs mathematically scale with damage output. |

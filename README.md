# Formalizacja teorii grup w Rocq

Projekt zawiera formalizację podstawowych pojęć z teorii grup z wykorzystaniem narzędzia Rocq.

## Opis projektu

Celem projektu jest implementacja podstawowych definicji i twierdzeń z teorii grup, takich jak:
- definicja grupy,
- definicja podgrupy,
- warstwy lewo- i prawostronne,
- własności elementu neutralnego,
- jednoznaczność elementu odwrotnego,
- prawa skracania,
- własności odwrotności.
- definicja grupy abelowej,
- twierdzenie: grupa Z3 jest abelowa,
- Przykłady grup i podgrup

## Struktura projektu

Plik `Groups.v` zawiera wszystkie zaimplementowane definicje, twierdzenia oraz przykłady formalizacji grup.
Plik `Raport.pdf` zawiera opis teoretyczny problemu, dokumentację kodu oraz omówienie wykorzystanych taktyk dowodowych.

## Zaimplementowane definicje

Projekt zawiera formalizację następujących pojęć:

- `is_group` – definicja grupy,
- `is_subgroup` – definicja podgrupy,
- `left_coset` – warstwa lewostronna,
- `right_coset` – warstwa prawostronna,
- `is_identity` – definicja elementu neutralnego,
- `is_inverse` – definicja elementu odwrotnego,
- `is_abelian_group` – definicja grupy abelowej.

## Zaimplementowane twierdzenia

W projekcie udowodniono następujące własności:

- jednoznaczność elementu neutralnego,
- jednoznaczność elementu odwrotnego,
- prawo skracania z lewej strony,
- prawo skracania z prawej strony,
- własność `(a⁻¹)⁻¹ = a`,
- własność `(ab)⁻¹ = b⁻¹a⁻¹`,
- grupa `(Z3, +)` jest abelowa,
- `(Z2, +)` jest podgrupą `(Z4, +)`.

## Przykłady grup

Projekt zawiera przykłady następujących grup:

- `Z3` – grupa cykliczna rzędu 3,
- `Z4` – grupa cykliczna rzędu 4,
- `Z2` jako podgrupa `Z4`.

## Wymagania

Projekt został napisany w Rocq/Coq i wykorzystuje standardową bibliotekę 
Require Import Ensembles.

## Możliwe rozwinięcia

Projekt można rozwinąć o wiele różnych twierdzeń i własności. Przykładowo można wprowadzić pojęcia podgrup normalnych, homomorfizmów grup albo wprowadzić grupy ilorazowe.

## Autorzy

Aniela Dąbrowska, Jarosław Piórkowski













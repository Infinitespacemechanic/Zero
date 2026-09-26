# Zero

Zero is a location.. and meeting point... a place... a destination...
this location has zero chickens.

> The red dots are the entire story. Everything else is just the function's way of traveling between those fixed locations.

## Build

```bash
lake update
lake build
```

Files:
- `Sine-pi-zeros-addresses.lean` — `sin(πx) = πx ∏ (1 - x²/n²)`, zeros as addresses, locked via `Real.tendsto_euler_sin_prod`
- `Zero on a line.lean` — zero as location, primes are just some addresses, chickens remain zero

## Lean version

- Lean 4.22.0-rc4
- Mathlib4 master (Euler sine product: `Real.tendsto_euler_sin_prod`, `Complex.tendsto_euler_sin_prod`)

All green, no sorrys.

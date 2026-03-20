I want to implement a SMT-like solver in Lean, in the Aeneas project, specialized for the
non-linear arithmetic that is found in cryptographic code (e.g., Montgomery reduction,
Barrett reduction, big num multiplication such as found in elliptic curves, NTT as found
in ML-KEM, etc.). It should be able to reason about non-linear arithmetic and also bitwise
operations as found in such operations. It doesn't have to be general, but should solve a
lot of the problems found in cryptographic implementations while being fast.

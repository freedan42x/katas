def bindable(
  A: ADT, 
  B: ADT, 
  bindings: Set[Tuple[ADT, ADT]]
) -> bool:
  if A.is_sum():
    return all(
      bindable(An, B, bindings) for An in A.subtypes
    )
  if B.is_sum():
    return any(
      bindable(A, Bn, bindings) for Bn in B.subtypes
    )
  if A.is_product() and B.is_product():
    a, b = A.subtypes, B.subtypes
    return all(
      bindable(An, Bn, bindings) for An, Bn in zip(a, b)
    ) and len(a) == len(b)
  return A == B or (A, B) in bindings

module Z3IndependentBooleanContext

module N = Z3BooleanNormalForm

let contextual_equivalent (s t:N.formula) : bool =
  let normalized_s = N.normalize false s in
  let normalized_t = N.normalize false t in
  if N.shape_equal 32 normalized_s normalized_t then true
  else if N.direct_contextual_equivalent s t then true
  else if (normalized_s <> s || normalized_t <> t) &&
          N.direct_contextual_equivalent normalized_s normalized_t then true
  else
    let negative_s = N.normalize true s in
    let negative_t = N.normalize true t in
    if (negative_s <> s || negative_t <> t) &&
       (negative_s <> normalized_s || negative_t <> normalized_t) &&
       N.direct_contextual_equivalent negative_s negative_t then true
    else
      let reversed_s = N.reverse s in
      let reversed_t = N.reverse t in
      if (reversed_s <> s || reversed_t <> t) &&
         (reversed_s <> normalized_s || reversed_t <> normalized_t) &&
         (reversed_s <> negative_s || reversed_t <> negative_t) &&
         N.direct_contextual_equivalent reversed_s reversed_t then true
      else
        let reversed_normalized_s = N.reverse normalized_s in
        let reversed_normalized_t = N.reverse normalized_t in
        (reversed_normalized_s <> s || reversed_normalized_t <> t) &&
        (reversed_normalized_s <> normalized_s || reversed_normalized_t <> normalized_t) &&
        (reversed_normalized_s <> negative_s || reversed_normalized_t <> negative_t) &&
        (reversed_normalized_s <> reversed_s || reversed_normalized_t <> reversed_t) &&
        N.direct_contextual_equivalent reversed_normalized_s reversed_normalized_t

// Copyright 1996  Michael E. Stillman

// This should probably be done by:
// (a) making a type Ring, that FreeModule, and res_poly
//     both can inherit from: but this is a bit of a kludge...
// (b) making a vector type with a next and coeff field, that
//     is then inherited by vecterm, resterm.
// Redefine:
// Ring
//    routines that should be implemented in this class:
//    add_to, compare, get_ring, remove
// Nterm *
//    fields of this structure type should include:
//    next, coeff

class polyheap
{
  const PolynomialRing *F;  // Our elements will be vectors in here
  const Ring *K;            // The coefficient ring
  ring_elem heap[GEOHEAP_SIZE];
  int top_of_heap;

 public:
  polyheap(const PolynomialRing *F);
  ~polyheap();

  void add(Nterm *p);
  Nterm *remove_lead_term();  // Returns nullptr if none.

  Nterm *value();  // Returns the linearized value, and resets the polyheap.

  Nterm *debug_list(int i)
  {
    return (heap[i]).poly_val;
  }  // DO NOT USE, except for debugging purposes!
};

inline polyheap::polyheap(const PolynomialRing *FF)
    : F(FF), K(FF->getCoefficientRing()), top_of_heap(-1)
{
  for (int i = 0; i < GEOHEAP_SIZE; i++) heap[i].poly_val = nullptr;
}

inline polyheap::~polyheap()
{
  // The user of this class must insure that all 'vecterm's
  // have been removed first.  Thus, we don't need to
  // do anything here.
}

inline void polyheap::add(Nterm *p)
{
  ring_elem pr = ring_elem(p);
  int len = F->n_terms(pr);
  int i = 0;
  while (len >= heap_size[i]) i++;

  F->add_to(heap[i], pr); // should consume pr too
  p = nullptr;

  len = F->n_terms(heap[i]);
  while (len >= heap_size[i])
    {
      i++;

      F->add_to(heap[i], heap[i-1]);
      heap[i - 1].poly_val = nullptr;
      len = F->n_terms(heap[i]);
    }
  if (i > top_of_heap) top_of_heap = i;
}

inline Nterm *polyheap::remove_lead_term()
{
  int lead_so_far = -1;
  for (int i = 0; i <= top_of_heap; i++)
    {
      if (heap[i].poly_val == nullptr) continue;
      if (lead_so_far < 0)
        {
          lead_so_far = i;
          continue;
        }
      int cmp = EQ;  // F->compare(heap[lead_so_far], heap[i]);
      if (cmp == GT) continue;
      if (cmp == LT)
        {
          lead_so_far = i;
          continue;
        }
      // At this point we have equality
      K->add_to(heap[lead_so_far].poly_val->coeff, heap[i].poly_val->coeff);
      Nterm *tmp = heap[i].poly_val;
      heap[i].poly_val = tmp->next;
      tmp->next = nullptr;
      ring_elem tmpr = ring_elem(tmp);
      F->remove(tmpr);

      if (K->is_zero(heap[lead_so_far].poly_val->coeff))
        {
          // Remove, and start over
          tmp = heap[lead_so_far].poly_val;
          heap[lead_so_far].poly_val = tmp->next;
          tmp->next = nullptr;
          ring_elem tmpr = ring_elem(tmp);
          F->remove(tmpr);
          lead_so_far = -1;
          i = -1;
        }
    }
  if (lead_so_far < 0) return nullptr;
  Nterm *result = heap[lead_so_far].poly_val;
  heap[lead_so_far].poly_val = result->next;
  result->next = nullptr;
  return result;
}

inline Nterm *polyheap::value()
{
  ring_elem result;
  result.poly_val = nullptr;
  for (int i = 0; i <= top_of_heap; i++)
    {
      if (heap[i].poly_val == nullptr) continue;
      ring_elem tmp2 = heap[i];
      F->add_to(result, tmp2);
      heap[i].poly_val = nullptr;
    }
  top_of_heap = -1;
  return result.poly_val;
}

// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// indent-tabs-mode: nil
// End:

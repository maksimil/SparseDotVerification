#include "lib.h"

Index SparseVectorDenseSize(const SparseVector *v) {
  Index i = 0;

  if (i < v->size) {
    Index r = v->indices[0];
    i = 1;

    /*@
      loop invariant \forall Index j; 0 <= j < i ==> v->indices[j] <= r;
      loop invariant i <= v->size;
      loop invariant \exists Index j; 0 <= j < i && v->indices[j] == r;
      loop assigns i, r;
      loop variant v->size - i;
    */
    while (i < v->size) {
      if (v->indices[i] >= r) {
        r = v->indices[i];
      }

      i++;
    }

    return r;
  } else {
    return 0;
  }
}

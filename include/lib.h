#ifndef SDV_H
#define SDV_H

#include <stddef.h>
#include <stdlib.h>

typedef size_t Index;
typedef double Scalar;

struct DenseVector {
  Scalar *values;
  Index size;
};

typedef struct DenseVector DenseVector;

/*@
  axiomatic DenseVectorInvariant {
    predicate DenseVectorInvariant{A}(DenseVector *v) =
      v->size >= 0 &&
      \valid(v->values + (0..v->size-1)) &&
      \separated(v, v->values);
  }
*/

struct SparseVector {
  Scalar *values;
  Index *indices;
  Index size;
};

typedef struct SparseVector SparseVector;

/*@
  axiomatic SparseVectorInvariant {
    predicate SparseVectorInvariant{A}(SparseVector *v) =
      v->size >= 0 &&
      \valid(v->values + (0..v->size-1)) &&
      \valid(v->indices + (0..v->size-1)) &&
      \separated(v, v->values, v->indices) &&
      (\forall Index i, j; (0 <= i < v->size && 0 <= j < v->size &&
        i != j) ==> v->indices[i] != v->indices[j]) &&
      (\forall Index i; 0 <= i < v->size ==> v->indices[i] >= 0);
  }
*/

/*@
  requires \valid(v) && SparseVectorInvariant(v);

  assigns \nothing;

  behavior Some:
    assumes v->size > 0;
    ensures \forall Index i; 0 <= i < v->size ==> v->indices[i] <= \result;
    ensures \exists Index i; 0 <= i < v->size && v->indices[i] == \result;

  behavior Empty:
    assumes v->size == 0;
    ensures \result == 0;

  complete behaviors;
  disjoint behaviors;
*/
Index SparseVectorDenseSize(const SparseVector *v);

#endif

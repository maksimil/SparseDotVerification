#ifndef SDV_H
#define SDV_H

#include <stddef.h>
#include <stdlib.h>

typedef size_t Index;
typedef double Scalar;

const Index INDEX_ONE = 1;

struct DenseVector {
  Scalar *values;
  Index size;
};

typedef struct DenseVector DenseVector;

/*@
  axiomatic DenseVector {
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
  axiomatic SparseVector {
    predicate SparseVectorInvariant{A}(SparseVector *v) =
      v->size >= 0 &&
      \valid(v->values + (0..v->size-1)) &&
      \valid(v->indices + (0..v->size-1)) &&
      \separated(v, v->values, v->indices) &&
      (\forall integer i, j; (0 <= i < v->size && 0 <= j < v->size &&
        i != j) ==> v->indices[i] != v->indices[j]) &&
      (\forall integer i; 0 <= i < v->size ==> v->indices[i] >= 0);

    logic integer SparseVectorDenseSize(SparseVector *v, integer m) =
      m > 0 ?
        (m <= v->size ?
          (SparseVectorDenseSize(v, m-1) > v->indices[m-1] ?
            SparseVectorDenseSize(v, m-1) : v->indices[m-1]) :
          SparseVectorDenseSize(v, m-1)) :
        0;

    logic integer SparseVectorDenseSize(SparseVector *v) =
      SparseVectorDenseSize(v, v->size);

    predicate SparseVectorDenseSizeValidTo{A}(integer n) =
      \forall SparseVector *v;
        (SparseVectorInvariant{A}(v) && n <= v->size) ==>
          (\forall integer i; 0 <= i < n ==>
            v->indices[i] <= SparseVectorDenseSize(v, n));

    lemma SparseVectorDenseSizeValidBase :
      SparseVectorDenseSizeValidTo(0);

    lemma SparseVectorDenseSizeValidStep :
      \forall integer n; n >= 0 ==>
        (SparseVectorDenseSizeValidTo(n) ==> 
          SparseVectorDenseSizeValidTo(n + 1));

    lemma SparseVectorDenseSizeValid :
      \forall integer n; n >= 0 ==> SparseVectorDenseSizeValidTo(n);
  }
*/

/*@
  requires \valid(v) && SparseVectorInvariant(v);

  assigns \nothing;

  ensures \result == SparseVectorDenseSize(v);

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

/*@
  requires \valid(v) && \valid(dense) &&
    SparseVectorInvariant(v) && DenseVectorInvariant(dense);
  requires dense->size > SparseVectorDenseSize(v);

  assigns \nothing;
*/
void SparseVectorToDense(const SparseVector *v, DenseVector *dense);

#endif

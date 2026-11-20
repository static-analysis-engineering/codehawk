/* Attributes on struct types and fields (data-structure invariants).
   Must compile cleanly; tools/check_cil_types.py checks where CIL attaches
   each attribute. Fields are referenced by name strings through a declared
   constructor (chk_fld): bare field names are not in scope (see
   reject/field_name.c). */
#include "../ch_terms_test.h"

/* T1: after the struct keyword: on the compinfo (cattr) */
struct __attribute__((chk_inv(rel_leq, chk_fld("len"), chk_fld("cap")))) s1 {
  unsigned len, cap;
};

/* T2: after the closing brace: on the compinfo (cattr) */
struct s2 { unsigned len, cap; }
  __attribute__((chk_inv(rel_leq, chk_fld("len"), 16)));

/* T3: on a field: on the fieldinfo (fattr) */
struct s3 {
  unsigned cap;
  unsigned len __attribute__((chk_inv(rel_leq, 0, chk_fld("cap"))));
};

/* T5: struct defined elsewhere (e.g. a project header), specified afterwards */
struct s5 { unsigned len, cap; };

/* T5a: redeclaration after the definition: accepted by gcc/clang, but CIL
   drops the attribute (s5's cattr stays empty) */
struct __attribute__((chk_inv(rel_leq, chk_fld("len"), chk_fld("cap")))) s5;

/* T5b: typedef carrier: on the TComp type the typedef names */
typedef struct s5 chk_inv_s5
  __attribute__((chk_inv(rel_leq, chk_fld("len"), chk_fld("cap"))));

/* T5c: function carrier: on the varinfo */
void chk_invariant_s5(struct s5 *)
  __attribute__((chk_inv(rel_leq, chk_fld("len"), chk_fld("cap"))));

/* T6: typedef of an anonymous struct (cFE style): the carrier names the
   typedef, so CIL attaches the attribute to TNamed (rec_t), not to TComp; the
   struct gets a generated name (__anonstruct_rec_t_<n>), so the invariant is
   keyed by the typedef name */
typedef struct { unsigned len, cap; } rec_t;
typedef rec_t chk_inv_rec_t
  __attribute__((chk_inv(rel_leq, chk_fld("len"), chk_fld("cap"))));

struct s1 g1; struct s2 g2; struct s3 g3; struct s5 g5; chk_inv_s5 g5b;
rec_t g6; chk_inv_rec_t g6b;
void use_types(void) { chk_invariant_s5(&g5); }

/* Must compile cleanly with gcc and clang (unknown-attribute warnings
   suppressed, everything else an error), and parse with CIL into
   structured trees (ACons/ABinOp/AInt/AStr). */
#include "../ch_terms_test.h"
typedef unsigned long size_t;

/* bare predicate name first, integer indices */
void a1(char *, const char *, size_t)
  __attribute__((chk_pre(deref_write, 1, 3)));

/* nested terms through declared constructors */
char *a2(char *, const char *, size_t)
  __attribute__((chk_pre(deref_read, 2, chk_min(3, chk_ntp(2) + 1))));

/* checked name form */
void a3(char *dst, const char *src)
  __attribute__((chk_pre(not_null, chk_arg(2, "src"))));

/* prefix position */
__attribute__((chk_pre(not_null, 1))) void a4(char *p);

/* return value as index 0 */
char *a5(char *) __attribute__((chk_post(not_null, 0)));

/* proposed CHB form replacing chk_pre(deref_read(ntp), 1) */
char *a6(char *) __attribute__((chk_pre(deref_read, 1, chk_ntp(1))));

/* string-encoded term: accepted, but CIL yields an opaque AStr */
void a7(char *, const char *, size_t)
  __attribute__((chk_pre(deref_read, 2, "min(3, ntp(2) + 1)")));

/* enum constant: accepted, but CIL folds it to AInt (name lost) */
enum ch_test_const { ch_test_return = 0 };
int a8(int) __attribute__((chk_post(not_null, ch_test_return)));

void use(void) {
  a1(0, 0, 0); a2(0, 0, 0); a3(0, 0); a4(0); a5(0); a6(0); a7(0, 0, 0); a8(0);
}

/* call to an undeclared term constructor: implicit declaration; a warning in
   gcc 11/12 and clang 14, an error by default in GCC 14 and clang 16 (run
   here with -Werror=implicit-function-declaration) */
typedef unsigned long size_t;
char *r(char *, const char *, size_t)
  __attribute__((chk_pre(deref_read, 2, min(3, ntpos(2) + 1))));

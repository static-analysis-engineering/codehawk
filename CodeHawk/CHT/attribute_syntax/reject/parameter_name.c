/* parameter names are out of scope in attribute arguments after the
   declarator (prototype scope, C11 6.2.1p4): error (undeclared) */
typedef unsigned long size_t;
void r(char *dst, const char *src, size_t n)
  __attribute__((chk_pre(deref_read, src, n)));

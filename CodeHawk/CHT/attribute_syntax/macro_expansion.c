/* attribute arguments are macro-expanded: a term named like a project
   macro is silently rewritten (checked with gcc -E) */
#define min(a, b) ((a) < (b) ? (a) : (b))
void m(char *, const char *, unsigned long)
  __attribute__((chk_pre(deref_read, 2, min(3, 4))));

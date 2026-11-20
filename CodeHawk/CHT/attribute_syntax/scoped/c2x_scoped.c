/* C2x scoped attributes: arguments are an unparsed balanced-token sequence,
   so gcc/clang (-std=gnu2x) accept anything; goblint-cil 2.0.6 has no grammar
   for [[ ]] and rejects the file. */
typedef unsigned long size_t;
[[chk::pre(deref_read, src, min(n, ntpos(src) + 1))]]
void s1(char *dst, const char *src, size_t n);
[[chk::post(eq, return, 0)]] int s2(int);

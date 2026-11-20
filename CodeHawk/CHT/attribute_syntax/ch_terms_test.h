/* Declarations of CodeHawk term constructors, as proposed for a shared
   CodeHawk header (CHC contracts design, CHB-4). They are never defined or
   called; they only make attribute arguments valid C expressions for
   gcc/clang. The chk_ prefix avoids collisions with project macros. */
#ifndef CH_TERMS_TEST_H
#define CH_TERMS_TEST_H
long chk_min(long, long);
long chk_ntp(int);
long chk_arg(int, const char *);
long chk_fld(const char *);
#endif

/* undeclared identifier in a non-first argument: error (undeclared) */
void r(char *p) __attribute__((chk_pre(deref_read, 1, nullterminated)));

/* field names are not ordinary identifiers (C11 6.2.3: separate name space
   per structure): error (undeclared) */
struct s { unsigned len, cap; } __attribute__((chk_inv(rel_leq, len, cap)));

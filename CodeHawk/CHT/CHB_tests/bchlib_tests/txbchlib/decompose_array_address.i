/* Data types used in the unit tests in bCHFlocTest.

   These signatures are directly parsed by CIL (without pre-processing), so
   this file should not include any macros or includes or any other construct
   usually handled by the pre-processor.
*/


struct x44_struct_t {
  int field0;
  int field4;
  char buffer[32];
  int field2c;
  int field30;
  int field34;
  int field38;
  int field3c;
  int fd;
  int msg;
};

struct x44_struct_t gv_5e1e1c_x44_array[64];

/* Function signatures used in the unit tests in bCHFunctionInterfaceTest.

   These signatures are directly parsed by CIL (without pre-processing), so
   this file should not include any macros or includes or any other construct
   usually handled by the pre-processor.
*/

int f_1(int i);

int f_2(int i, int j);

int f_3(int i, double d, int j);

int f_4(float x, float y, float z, int a, int b);

int f_5(float x, double y, float z, float t);

int f_6(int a, int b, int c, int d, int e);


struct struct1_t {
  int fld1;
  int fld2;
  int fld3;
};

int f_7(struct struct1_t a);


struct struct2_t {
    void* data;
    unsigned short type;
    unsigned short position;
};

int f_8(struct struct2_t a);

int f_9(int a, int b, struct struct2_t c);

int f_10(int a, int b, int c, struct struct2_t d);


struct struct3_t
{
    int fld1;
    char fld2;
    char fld3;
    char fld4;
    char fld5;
    char data[0x8];
};


int f_11(struct struct3_t a);

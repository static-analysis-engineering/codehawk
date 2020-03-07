## Naming conventions for the Java Analyzer

### General

#### Variables
Variables of the following types are typically referred to with a fixed
name to make them easy to recognize:

Data structures that provide information on the core entities in a Java
program (defined in jchpre/jCHPreAPI):

- *class_info_int*: **cInfo**
- *field_info_int*: **fInfo**
- *instruction_info_int*: **iInfo**
- *method_info_int*: **mInfo**

Data structures for various signatures (defined in jchlib/jCHBasicTypesAPI) and
their index values (type int):

- *class_name_int*: **cn**, with index **cnix**

- *class_field_signature_int*: **cfs**, with index **cfsix**
- *field_signature_int*: **fs**, with index **fsix**

- *class_method_signature_int*: **cms**, with index **cmsix**
- *method_signature_int*: **ms**, with index **msix**

## Library Function Summaries

### Contents
- [Summary specification](#summary-specification)
- [Organization](#organization)
- [Format of predicates](#format-of-predicates)
- [Format of summaries](#format-of-summaries)
- [Predicate and function symbols](#predicate-and-function-symbols)


### Summary specification

Library function summaries specify:
- **preconditions**: predicates on function parameters (e.g., ```not-null```); these
  conditions are converted into primary proof obligations on the function arguments
  at all call sites of the function;
- **postconditions**: predicates on the return value, possibly in relation to function
  parameters; postconditions can be split in regular postconditions (the normal case)
  and error-postconditions (the value returned to indicate an error-condition).
  Postconditions are converted into guarantees on the return value from the function
  at all call sites of the function;
- **side effects**: predicates on the function parameters that describe a frame
  condition. By default the analyzer assumes that values reachable by pointer
  arguments may be changed arbitrarily by the function, or that any memory pointed
  to may be freed. A frame condition generally restricts the modifications that may
  be performed by the function. These conditions are converted into guarantees that
  hold after the function returns, at every call site.

### Organization

Library function summaries are written in XML, a separate file for each summary, with
the name of the function as filename, e.g., ```strcpy.xml```. The files are organized
by header file.

### Format of predicates

The format of the predicates, and of expressions in general, roughly follows the
schema of [MathML](https://www.w3.org/Math/), using the following constructs:

- *constant literals*: numeric constants are specified with the tag ```cn```, e.g.,
  ```
  <cn>256</cn>
  ```
- *symbolic values*: symbolic constants and references to function parameters are
  specified with the tag ```ci```, e.g.,
  ```
  <ci>MAXUINT16</ci>
  ```
  to specify the maximum value of an unsigned 16-bit integer, or
  ```
  <ci>dest</ci>
  ```
  to refer to the destination parameter of a function. The name  ```dest``` of the
  parameter must be present in the function summary to be recognized.
  
- *function application*: the application of functions or predicates is specified
  with the tag ```apply```, with child elements the name of the predicate or function
  and the arguments to the predicate or function. Nullary functions and predicate
  still use ```apply```. An example of a nullary predicate is
  ```
  <apply><preserves-all-memory/></apply>
  ```
  to specify that a function does not free any memory. An example of a binary
  predicate is
  ```
  <apply>
    <geq/>
    <return/>
    <cn>0</cn>
  </apply>
  ```
  to specify that the return value is greater than or equal to zero. The full expression
  is enclosed by a ```math``` tag, e.g.,
  ```
  <math>
    <apply>
      <geq/>
      <return/>
      <cn>0</cn>
    </apply>
  </math>
  ```   
### Format of summaries
The outline of a function summary in XML is as follows:
```
<codehawk-summary-file>
  <header date="YYYY-MM-DD HH;MM:SS"/>
  <function-summary name="function-name">
    <parameters>
      <par name="parameter name1" nr="1"/>
      <par name="parameter name2" nr="2"/>
      ....
    </parameters>
    <preconditions>
      <pre>
        ... predicate
      </pre>
      <pre>
        ... predicate
      </pre>
      ...
    </preconditions>
    <postconditions>
      <post>
        ... predicate
      </post>
      <post>
        ... predicate
      </post>
      ...   
      <error-post>
        ... predicate
      </error-post>
    </postconditions>
    <sideeffects>
      <sideeffect>
	    ... predicate
	  </sideeffect>
	    ...
	</sideeffects>
  </function-summary>
</codehawk-summary-file>	
```

### Predicate and function symbols

#### Standard predicate and function symbols (from MathML)

Comparison binary predicates:
- **lt**: less than
- **leq**: less than or equal to
- **gt**: greater than
- **geq**: greater than or equal to
- **eq**: equal
- **neq**: not equal

Arithmetic binary functions:
- **plus**: addition
- **minus**: subtraction
- **times**: multiplication
- **divide**: division

#### Term constructors

Terminal values:
- **cn** *integer*: numeric value
- **ci** *name*: symbolic constant or reference to parameter or global variable
- **runtime-value**: unknown value determined at runtime (e.g., user input)
- **choice**: any value between an optional lowerbound and upperbound,
    specified by attributes "lb" and "ub"
- **return**: return value
	
Non-terminals:
- **addressed-value** ```<term>```: the value addressed by the term
- **index-size** ```<term>```: the size of the term given in the type units of the term
- **byte-size**  ```<term>```: the sixe of the term given in bytes
- **region** ```<term>```: the memory region that term belongs to
- **null-terminator-pos** ```<term>```: the position of the null-terminator in term
- **size-of-type** ```<term>```: the size of the type of term, in bytes

#### Predicates

##### Nullary predicates:
- **false**: (postcondition) the function does not return
- **functional**: (sideeffect) the function is pure functional (no sideeffects)
- **preserves-all-memory**: (sideeffect) the function does not free any memory

##### Unary predicates:
- **allocation-base** *t*: (postcondition) *t* points
    to the starting address of dynamically allocated memory (which is
    legal to be freed)
- **const** *t*: (sideeffect) the function does not change the value pointed at
  at by *t*
- **frees** *t*: (sideeffect) the function frees the memory pointed at by *t*
- **global-address** *t*: (postcondition) the term points at a global address
  (as, for example, returned by <code>getenv</code> in stdlib)
- **initializes** *t*: (sideeffect or postcondition) the function initializes
  a field or array
  element of the object pointed at by *t*. A field is specified by the
  attribute *field* with a name, an array index is specified by the attribute
  *index* with a nonnegative number (Note: syntax to be changed)
- **initialized** *t*: (postcondition) the location pointed at by the return
  value is initialized
- **invalidates** *t*: (sideeffect) the function invalidates the resource pointed
  at by *t* (examples: dirent/closedir, unistd/close, netdb/freeaddrinfo)
- **not-null** *t*: (pre- or postcondition) term *t* is not NULL 
- **not-zero** *t*: (pre- or postcondition) term *t* is not zero
- **non-negative** *t*: (pre- or postcondition) term *t* is non-negative
- **null** *t*: (pre- or postcondition) term *t* is NULL (usually used in error-post)
- **null-terminated** *t*: (pre- or postcondition) term *t* is null-terminated
- **format-string** *t*: (precondition) term *t* is a format string (which imposes
  the proof obligation that it be a string literal)
- **preserves-memory** *t*: (sideeffect) the memory pointed at by *t* is not freed
- **preserves-all-memory-x** *t*: (sideeffect) the function does not free any
  memory except, possibly, the memory pointed at by *t*
- **tainted** *t*: (postcondition) the return value may be tainted (that is, have
  an arbitrary value not controlled by the program). An optional lower and upper
  bound can be specified with the attributes *lb* and *ub", whose values should be
  either a numerical value or a symbolic constant.

##### Binary predicates:
- **block-write** *t1* *t2*: (sideeffect) the function writes at most *t2* bytes
  to the memory pointed at by *t1*
- **buffer** *t1* *t2*: (postcondition) *t1* points to a memory region of size at
  least *t2* bytes
- **deref-read** *t1* *t2*: (precondition) *t1* is not NULL and points at a
  memory region of at least *t2* bytes that has been initialized (that is, is
  legal to be read)
- **deref-read-null** *t1* *t2*: (precondition) same as **deref-read**, except
  that *t1* is allowed to be NULL
- **deref-write** *t1* *t2*: (precondition) *t1* is not NULL and points at a
  memory region of at least *t2* bytes
- **deref-write-null** *t1* *t2*: (precondition) same as **deref-write**, except
  that *t1* is allowed to be NULL
- **initializes-range** *t1* *t2*: (sideeffect) the function initializes
  at least *t2* bytes of the memory pointed to by *t1* (examples: string/memcpy,
  string/memset)
- **no-overlap** *t1* *t2*: (precondition) the memory regions pointed to by  *t1*
  and *t2* do not overlap
- **rev-buffer** *t1* *t2*: (postcondition) *t1* points to an address within a
  memory region that is at an offset of at least *t2* bytes from the start of the
  region


### Symbolic constants
The following symbolic constants are currently recognized:

| name | value |
| :--- |  ---: |
| **MININT8** | -128 |
| **MAXINT8** | 127 |
| **MAXUINT8** | 255 |
| **MININT16** | -32768 |
| **MAXINT16** | 32767 |
| **MAXUINT16** | 65535 |
| **MININT32** | -2147483648 |
| **MAXINT32** | 2147483647 |
| **MAXUINT32** | 4294967295 |
| **MININT64** | -9223372036854775808 |
| **MAXINT64** | 9223372036854775807 |
| **MAXUINT64** | 18446744073709551615 |

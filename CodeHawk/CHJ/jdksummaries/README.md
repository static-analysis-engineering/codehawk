## JDK Summaries

Class and method summaries are provided for a large number of classes
The summaries
are represented in XML, with one XML file per class file; the files are stored
according to the class file hierarchy. The following table presents a summary
of the number of methods currently summarized per package. A method is
considered summarized if it includes taint transfer information. Some
methods also have pre- and post conditions and information about string
arguments that require to have a certain form and arguments that represent
the size of a particular resource, usually memory. 

| package | classes | methods | preconditions | postconditions | string sinks | resource sinks | 
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | 
com.sun.net.httpserver | 10 | 64 | 0 | 0 | 0 | 0 | 
java.applet | 2 | 26 | 0 | 1 | 0 | 0 | 
java.awt | 82 | 1337 | 69 | 158 | 11 | 0 | 
java.awt.color | 1 | 12 | 0 | 1 | 0 | 0 | 
java.awt.datatransfer | 7 | 55 | 3 | 13 | 5 | 0 | 
java.awt.dnd | 1 | 0 | 0 | 0 | 0 | 0 | 
java.awt.event | 29 | 74 | 3 | 8 | 0 | 0 | 
java.awt.font | 9 | 73 | 4 | 11 | 0 | 0 | 
java.awt.geom | 30 | 441 | 34 | 30 | 0 | 0 | 
java.awt.image | 37 | 406 | 57 | 97 | 0 | 12 | 
java.awt.image.renderable | 3 | 32 | 0 | 0 | 0 | 0 | 
java.awt.print | 4 | 21 | 0 | 0 | 0 | 0 | 
java.beans | 27 | 165 | 5 | 24 | 18 | 4 | 
java.io | 74 | 689 | 37 | 161 | 26 | 13 | 
java.lang | 89 | 1240 | 323 | 471 | 76 | 13 | 
java.lang.annotation | 4 | 5 | 2 | 3 | 2 | 0 | 
java.lang.invoke | 5 | 87 | 48 | 35 | 7 | 0 | 
java.lang.management | 6 | 46 | 0 | 8 | 2 | 0 | 
java.lang.ref | 5 | 15 | 1 | 0 | 0 | 0 | 
java.lang.reflect | 22 | 189 | 62 | 19 | 0 | 0 | 
java.math | 4 | 129 | 7 | 69 | 1 | 0 | 
java.net | 49 | 454 | 18 | 54 | 43 | 2 | 
java.nio | 11 | 152 | 10 | 53 | 0 | 6 | 
java.nio.channels | 28 | 97 | 6 | 37 | 0 | 0 | 
java.nio.channels.spi | 4 | 23 | 0 | 1 | 0 | 0 | 
java.nio.charset | 12 | 75 | 5 | 24 | 0 | 0 | 
java.nio.charset.spi | 1 | 1 | 0 | 0 | 0 | 0 | 
java.nio.file | 23 | 106 | 5 | 31 | 8 | 0 | 
java.nio.file.attribute | 5 | 16 | 1 | 2 | 1 | 0 | 
java.rmi | 4 | 14 | 1 | 0 | 5 | 0 | 
java.rmi.registry | 3 | 7 | 2 | 0 | 2 | 0 | 
java.rmi.server | 14 | 27 | 0 | 1 | 0 | 0 | 
java.security | 63 | 330 | 20 | 17 | 23 | 0 | 
java.security.cert | 32 | 236 | 23 | 40 | 22 | 0 | 
java.security.spec | 14 | 55 | 11 | 11 | 0 | 0 | 
java.sql | 40 | 198 | 0 | 25 | 22 | 0 | 
java.text | 28 | 326 | 35 | 44 | 14 | 0 | 
java.time | 8 | 182 | 24 | 132 | 8 | 0 | 
java.time.chrono | 3 | 0 | 0 | 0 | 0 | 0 | 
java.time.format | 1 | 4 | 0 | 3 | 0 | 0 | 
java.time.temporal | 4 | 0 | 0 | 0 | 0 | 0 | 
java.util | 78 | 1117 | 151 | 351 | 11 | 20 | 
java.util.concurrent | 31 | 309 | 61 | 91 | 1 | 33 | 
java.util.concurrent.atomic | 10 | 56 | 0 | 5 | 1 | 0 | 
java.util.concurrent.locks | 5 | 40 | 0 | 15 | 0 | 1 | 
java.util.function | 13 | 2 | 0 | 0 | 0 | 0 | 
java.util.jar | 2 | 14 | 3 | 4 | 3 | 0 | 
java.util.logging | 9 | 122 | 2 | 16 | 53 | 0 | 
java.util.regex | 3 | 36 | 0 | 9 | 3 | 0 | 
java.util.stream | 7 | 36 | 0 | 0 | 0 | 0 | 
java.util.zip | 12 | 118 | 17 | 24 | 1 | 6 | 
javax.accessibility | 10 | 35 | 0 | 14 | 2 | 0 | 
javax.activation | 2 | 19 | 0 | 0 | 1 | 0 | 
javax.annotation.processing | 7 | 34 | 0 | 4 | 0 | 0 | 
javax.crypto | 14 | 115 | 4 | 25 | 13 | 0 | 
javax.crypto.spec | 8 | 35 | 7 | 9 | 0 | 0 | 
javax.imageio | 8 | 171 | 20 | 36 | 9 | 0 | 
javax.imageio.metadata | 2 | 32 | 0 | 0 | 1 | 0 | 
javax.imageio.plugins.jpeg | 3 | 21 | 2 | 8 | 0 | 0 | 
javax.imageio.spi | 5 | 24 | 0 | 0 | 1 | 0 | 
javax.imageio.stream | 2 | 0 | 0 | 0 | 0 | 0 | 
javax.lang.model | 3 | 11 | 4 | 3 | 2 | 0 | 
javax.lang.model.element | 9 | 37 | 2 | 9 | 3 | 0 | 
javax.lang.model.type | 2 | 8 | 1 | 2 | 1 | 0 | 
javax.lang.model.util | 2 | 25 | 0 | 10 | 0 | 0 | 
javax.management | 21 | 142 | 27 | 15 | 26 | 0 | 
javax.management.openmbean | 4 | 28 | 1 | 12 | 1 | 0 | 
javax.naming | 18 | 96 | 22 | 20 | 21 | 0 | 
javax.naming.event | 5 | 0 | 0 | 0 | 0 | 0 | 
javax.naming.spi | 6 | 0 | 0 | 0 | 0 | 0 | 
javax.net | 2 | 13 | 0 | 0 | 0 | 0 | 
javax.net.ssl | 29 | 101 | 4 | 18 | 2 | 0 | 
javax.security.auth | 6 | 33 | 10 | 11 | 5 | 0 | 
javax.security.auth.callback | 3 | 18 | 0 | 0 | 7 | 0 | 
javax.security.auth.kerberos | 6 | 65 | 4 | 10 | 8 | 0 | 
javax.security.auth.login | 1 | 6 | 0 | 0 | 3 | 0 | 
javax.security.auth.x500 | 1 | 9 | 1 | 0 | 1 | 0 | 
javax.sound.sampled | 7 | 24 | 0 | 7 | 0 | 0 | 
javax.sql | 16 | 7 | 0 | 0 | 0 | 0 | 
javax.swing | 98 | 1440 | 47 | 170 | 33 | 4 | 
javax.swing.border | 3 | 8 | 0 | 0 | 0 | 0 | 
javax.swing.event | 25 | 51 | 0 | 4 | 0 | 0 | 
javax.swing.filechooser | 1 | 1 | 0 | 0 | 0 | 0 | 
javax.swing.plaf | 2 | 14 | 2 | 6 | 0 | 0 | 
javax.swing.plaf.basic | 1 | 8 | 3 | 1 | 0 | 0 | 
javax.swing.plaf.metal | 1 | 6 | 3 | 1 | 0 | 0 | 
javax.swing.table | 9 | 85 | 0 | 6 | 0 | 0 | 
javax.swing.text | 32 | 200 | 3 | 22 | 0 | 0 | 
javax.swing.text.html | 7 | 66 | 5 | 5 | 0 | 0 | 
javax.swing.tree | 6 | 77 | 6 | 35 | 0 | 0 | 
javax.tools | 6 | 21 | 1 | 2 | 1 | 0 | 
javax.transaction.xa | 1 | 3 | 0 | 0 | 0 | 0 | 
javax.xml.bind | 6 | 1 | 0 | 0 | 1 | 0 | 
javax.xml.datatype | 4 | 22 | 5 | 3 | 0 | 0 | 
javax.xml.namespace | 1 | 10 | 4 | 0 | 7 | 0 | 
javax.xml.parsers | 6 | 45 | 4 | 7 | 4 | 0 | 
javax.xml.stream | 12 | 38 | 0 | 1 | 0 | 0 | 
javax.xml.transform | 11 | 48 | 0 | 8 | 0 | 0 | 
javax.xml.transform.dom | 2 | 18 | 0 | 0 | 5 | 0 | 
javax.xml.transform.sax | 4 | 19 | 7 | 5 | 2 | 0 | 
javax.xml.transform.stream | 2 | 28 | 5 | 6 | 6 | 0 | 
javax.xml.validation | 1 | 6 | 3 | 0 | 0 | 0 | 
javax.xml.xpath | 1 | 4 | 0 | 0 | 0 | 0 | 
org.ietf.jgss | 2 | 10 | 0 | 1 | 0 | 0 | 
org.w3c.dom | 10 | 40 | 2 | 18 | 0 | 0 | 
org.xml.sax | 15 | 61 | 4 | 16 | 6 | 0 | 
org.xml.sax.ext | 1 | 4 | 0 | 1 | 5 | 0 | 
org.xml.sax.helpers | 8 | 102 | 1 | 20 | 47 | 0 | 
sun.net.www | 2 | 0 | 0 | 0 | 0 | 0 | 
sun.net.www.protocol.file | 1 | 0 | 0 | 0 | 0 | 0 | 
sun.security.util | 1 | 0 | 0 | 0 | 0 | 0 | 
| total  | 1452 | 12804 | 1264 | 2650 | 593 | 114 | 


### Preconditions

Preconditions are specified as safety conditions that need to hold
to avoid that a particular exception is thrown. The following table
shows the distribution of preconditions over the different types of
exceptions covered.

| exception | number of preconditions |
| :--- |  ---: |
| java.awt.IllegalComponentStateException | 3 | 
| java.awt.image.RasterFormatException | 2 | 
| java.lang.ArithmeticException | 24 | 
| java.lang.ArrayIndexOutOfBoundsException | 68 | 
| java.lang.ArrayStoreException | 1 | 
| java.lang.IllegalArgumentException | 272 | 
| java.lang.IndexOutOfBoundsException | 147 | 
| java.lang.NegativeArraySizeException | 17 | 
| java.lang.NullPointerException | 639 | 
| java.lang.StringIndexOutOfBoundsException | 74 | 
| java.net.MalformedURLException | 1 | 
| java.security.InvalidParameterException | 1 | 
| java.time.DateTimeException | 12 | 
| java.util.EmptyStackException | 2 | 
| javax.management.MalformedObjectNameException | 1 | 

### Summary Content

A class summary contains the following information:
- class name (e.g., String)
- package (e.g., java.lang)
- indication if it is final
- indication if it is abstract
- indication if it is immutable
- list of interfaces the class implements, if any
- list of public fields, if any
- list of public/protected instance constructor summaries, if any
- list of public/protected method summaries
- list of signatures of inherited methods, with defining class

A method summary contains the following information:
- method name
- method signature
- method visibility (public or protected)
- indication if the method is abstract
- indication if the method is final
- list of exceptions thrown, possibly associated with safety conditions
- taint transfer information
- postconditions (optional)
- string/resource sinks (optional)

A constructor summary contains the same information as a method
summary except that it does not have a name.

### Postconditions
Postconditions are represented in MathML.

### Safety conditions
Exceptions thrown can be associated with safety conditions, whose
conjunction, if true, ensures that the exception is not thrown.
Safety conditions are also expressed in MathML.

### String sinks
Some use cases rely on tracking the use of strings and tracking
their purpose and destinations. Summaries can include so-called
string sinks that associate a string argument, indicated by the
*arg* attribute with a *form* attribute
describing
its intended/required format, and a *dest* attribute
describing its purpose
or intended destination. These string sinks are still in an
experimental phase, and have been added only to a limited number of
summaries. These sinks will be most useful if the forms and dests
are limited to a relatively small set of keywords. So far the
following have been used.

#### Forms
- *action command*: as used in the setActionCommand in javax.swing
- *algorithm name*: as used in several javax.crypto and java.security methods
- *attribute name*: XML or beans attribute name
- *attribute type*: XML attribute type
- *attribute value*: XML attribute value
- *bean name*: name of property, method or event in beans
- *button text*: text to be displayed on a display button
- *character encoding*: name of a character encoding
- *class name*: fully qualified name of a java class
- *column label*: as used in SQL
- *composite name*: as used in javax/naming
- *cryptographic service*: e.g., Signature, MessageDigest, Mac, Cipher
- *description*: free-form description of entity
- *element tag*: tag of an XML element
- *encoded*: encoded string
- *environment variable*: name of environment variable
- *entity name*: name of entity in XML
- *enum constant*: string representation of enum
- *field name*: name of a java class field
- *file access mode*: file access mode
- *file attribute*: attribute of a file
- *file extension*: file extension
- *filename*: name of file
- *format-string*: string must be a valid format string
- *hostname*: name of a host on the network
- *identifier*: a name used to identify an entity for later reference
- *localized name*: a local name given to an accessible object
- *logger name*: name of a logger (usually a package name)
- *method name*: name of a java method
- *mime type*: content type for editing
- *namespace prefix*: used in XML tags
- *none*: no specific form required, e.g., for property values
- *notation name*: name to describe a notation in an XML document
- *number*: string should be able to be converted to a number
- *package name*: name of a java package
- *password*: password for login
- *pathname*: name of file or directory
- *processing data*: data associated with processing instruction in XML
- *processing instruction*: description of action to be taken in XML
- *property name*: as used in property/value maps or registries
- *provider name*: as used in factory methods
- *regex*: string is used as regular expression
- *resource name*: name of a resource or resource bundle
- *system property*: name of a system-wide property
- *title*: title for display elements
- *tooltip text*: text to be displayed as tool tip
- *tree pattern*: pattern used to extract data from parse trees
- *URI*: identified as such in several methods in org.xml.sax and
  javax.xml methods
- *URL*: identified as such in several methods in javax.swing.
- *username*: user name for login, etc.
- *XML tag*: element tag in XML


#### Destinations
- *accessibility*: java accessibility objects
- *authentication*: string is the subject of authentication
- *beans*: java beans properties
- *component retrieval*: retrieval of component based on component  name
- *console*: output destined for a console
- *display*: display to the user in a GUI
- *dynamic loading*: string is involved in creating classes to be
  loaded dynamically
- *enum value*: retrieval of numeric value of enum constant
- *field value access*: obtain constant field value by field name
- *logger*: information sent to a logger
- *login*: strings provided as username and password
- *event handling*: string is used to trigger or notify another
  component
- *mac*: generation of a MAC
- *matching*: general pattern matching against a regex
- *property value*: value of a mapped property
- *property retrieval*: string is used to obtain a mapped value
- *property set*: string is used to map a value
- *random*: generation of a random number
- *reflection*: string is used to retrieve an entity by reflection
- *retrieve content*: string is used to retrieve remove content
- *sanitize*: string is subjected to sanitization
- *xml*: XML document handling


### Resource sinks
Some use cases rely on tracking usage or consumption of a particular
resource. Summaries can include resource sinks that associate an
argument (usually a scalar like an int or long) with a *form*
attribute describing the resource. These resource sinks are still in an
experimental phase, and have been added only to a limited  number
of summaries. The following *form* attributes are currently
recognized:

- *memory*: used in allocation of memory, e.g., for arrays, hash
  tables, etc.
- *time*: used in timer expiration times or sleep times
- *threads*: number of threads created, e.g., for a thread pool
- *filesize*: size of file created

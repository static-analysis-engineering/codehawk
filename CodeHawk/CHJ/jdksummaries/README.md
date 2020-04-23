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
java.awt | 82 | 1278 | 67 | 158 | 10 | 0 | 
java.awt.color | 1 | 12 | 0 | 1 | 0 | 0 | 
java.awt.datatransfer | 7 | 55 | 3 | 13 | 5 | 0 | 
java.awt.dnd | 1 | 0 | 0 | 0 | 0 | 0 | 
java.awt.event | 29 | 74 | 3 | 8 | 0 | 0 | 
java.awt.font | 9 | 73 | 4 | 11 | 0 | 0 | 
java.awt.geom | 30 | 431 | 34 | 30 | 0 | 0 | 
java.awt.image | 37 | 402 | 57 | 87 | 0 | 12 | 
java.awt.image.renderable | 3 | 32 | 0 | 0 | 0 | 0 | 
java.awt.print | 4 | 21 | 0 | 0 | 0 | 0 | 
java.beans | 27 | 165 | 5 | 24 | 18 | 4 | 
java.io | 74 | 689 | 28 | 161 | 26 | 10 | 
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
java.time | 8 | 138 | 3 | 92 | 1 | 0 | 
java.time.chrono | 3 | 0 | 0 | 0 | 0 | 0 | 
java.time.format | 1 | 0 | 0 | 0 | 0 | 0 | 
java.time.temporal | 4 | 0 | 0 | 0 | 0 | 0 | 
java.util | 78 | 1110 | 123 | 350 | 11 | 19 | 
java.util.concurrent | 31 | 298 | 53 | 89 | 1 | 33 | 
java.util.concurrent.atomic | 10 | 56 | 0 | 5 | 1 | 0 | 
java.util.concurrent.locks | 5 | 40 | 0 | 15 | 0 | 1 | 
java.util.function | 13 | 2 | 0 | 0 | 0 | 0 | 
java.util.jar | 2 | 14 | 3 | 4 | 3 | 0 | 
java.util.logging | 9 | 122 | 2 | 16 | 53 | 0 | 
java.util.regex | 3 | 36 | 0 | 9 | 3 | 0 | 
java.util.stream | 7 | 36 | 0 | 0 | 0 | 0 | 
java.util.zip | 12 | 111 | 6 | 24 | 0 | 0 | 
javax.accessibility | 2 | 21 | 0 | 13 | 2 | 0 | 
javax.activation | 2 | 13 | 0 | 0 | 0 | 0 | 
javax.annotation.processing | 7 | 34 | 0 | 4 | 0 | 0 | 
javax.crypto | 9 | 85 | 1 | 18 | 6 | 0 | 
javax.crypto.spec | 3 | 10 | 0 | 3 | 0 | 0 | 
javax.imageio | 1 | 31 | 17 | 24 | 9 | 0 | 
javax.imageio.plugins.jpeg | 1 | 4 | 0 | 2 | 0 | 0 | 
javax.imageio.stream | 1 | 0 | 0 | 0 | 0 | 0 | 
javax.lang.model | 1 | 3 | 0 | 0 | 0 | 0 | 
javax.lang.model.element | 7 | 31 | 0 | 5 | 2 | 0 | 
javax.lang.model.type | 2 | 8 | 0 | 2 | 1 | 0 | 
javax.lang.model.util | 1 | 15 | 0 | 0 | 0 | 0 | 
javax.naming | 4 | 21 | 0 | 8 | 2 | 0 | 
javax.net | 2 | 13 | 0 | 0 | 0 | 0 | 
javax.net.ssl | 18 | 89 | 2 | 9 | 0 | 0 | 
javax.security.auth | 1 | 0 | 0 | 0 | 0 | 0 | 
javax.sound.sampled | 7 | 24 | 0 | 7 | 0 | 0 | 
javax.swing | 63 | 1095 | 28 | 147 | 28 | 0 | 
javax.swing.border | 3 | 8 | 0 | 0 | 0 | 0 | 
javax.swing.event | 16 | 26 | 0 | 4 | 0 | 0 | 
javax.swing.plaf | 1 | 14 | 2 | 6 | 0 | 0 | 
javax.swing.table | 7 | 58 | 0 | 3 | 0 | 0 | 
javax.swing.text | 6 | 108 | 0 | 10 | 0 | 0 | 
javax.swing.tree | 6 | 77 | 6 | 35 | 0 | 0 | 
javax.tools | 3 | 8 | 0 | 0 | 0 | 0 | 
javax.xml.bind | 1 | 0 | 0 | 0 | 0 | 0 | 
javax.xml.parsers | 5 | 39 | 4 | 7 | 4 | 0 | 
javax.xml.transform | 5 | 35 | 0 | 6 | 0 | 0 | 
javax.xml.transform.dom | 1 | 7 | 0 | 0 | 2 | 0 | 
javax.xml.transform.stream | 1 | 12 | 0 | 3 | 2 | 0 | 
org.w3c.dom | 10 | 40 | 2 | 18 | 0 | 0 | 
org.xml.sax | 12 | 56 | 0 | 16 | 6 | 0 | 
org.xml.sax.helpers | 3 | 44 | 0 | 15 | 46 | 0 | 
sun.net.www | 2 | 0 | 0 | 0 | 0 | 0 | 
sun.net.www.protocol.file | 1 | 0 | 0 | 0 | 0 | 0 | 
sun.security.util | 1 | 0 | 0 | 0 | 0 | 0 | 
| total  | 1184 | 11142 | 1033 | 2408 | 470 | 100 | 


### Preconditions

Preconditions are specified as safety conditions that need to hold
to avoid that a particular exception is thrown. The following table
shows the distribution of preconditions over the different types of
exceptions covered.

| exception | number of preconditions |
| :--- |  ---: |
| java.awt.image.RasterFormatException | 2 | 
| java.lang.ArithmeticException | 24 | 
| java.lang.ArrayIndexOutOfBoundsException | 55 | 
| java.lang.ArrayStoreException | 1 | 
| java.lang.IllegalArgumentException | 212 | 
| java.lang.IndexOutOfBoundsException | 147 | 
| java.lang.NegativeArraySizeException | 17 | 
| java.lang.NullPointerException | 497 | 
| java.lang.StringIndexOutOfBoundsException | 74 | 
| java.net.MalformedURLException | 1 | 
| java.security.InvalidParameterException | 1 | 
| java.util.EmptyStackException | 2 | 

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
Expressions thrown can be associated with safety conditions, whose
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

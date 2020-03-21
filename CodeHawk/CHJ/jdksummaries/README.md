## JDK Summaries

Class and method summaries are provided for a large number of classes
(currently 834 classes and interfaces with 8946 methods). The summaries
are represented in XML, with one XML file per class file; the files are stored
according to the class file hierarchy.

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
string sinks that associate a string argument with a *form* describing
its intended/required format, and a *dest* describing its purpose
or intended destination. These string sinks are still in an
experimental phase, and have been added only to a limited number of
summaries. These sinks will be most useful if the forms and dests
are limited to a relatively small set of keywords. So far the
following have been used.

#### Forms
- *action command*: as used in the setActionCommand in javax.swing
- *algorithm name*: as used in several javax.crypto methods
- *attribute name*: XML or beans attribute name
- *attribute type*: XML attribute type
- *attribute value*: XML attribute value
- *bean name*: name of property, method or event in beans
- *button text*: text to be displayed on a display button
- *character encoding*: name of a character encoding
- *class name*: fully qualified name of a java class
- *description*: free-form description of entity
- *encoded*: encoded string
- *environment variable*: name of environment variable
- *entity name*: name of entity in XML
- *enum constant*: string representation of enum
- *field name*: name of a java class field
- *file access mode*: file access mode
- *file attribute*: attribute of a file
- *file extension*: file extension
- *filename*: name of file
- *identifier*: a name used to identify an entity for later reference
- *localized name*: a local name given to an accessible object
- *logger name*: name of a logger (usually a package name)
- *method name*: name of a java method
- *mime type*: content type for editing
- *namespace prefix*: used in XML tags
- *none*: no specific form required, e.g., for property values
- *notation name*: name to describe a notation in an XML document
- *package name*: name of a java package
- *pathname*: name of file or directory
- *processing data*: data associated with processing instruction in XML
- *processing instruction*: description of action to be taken in XML
- *property name*: as used in property/value maps or registries
- *regex*: string is used as regular expression
- *resource name*: name of a resource or resource bundle
- *system property*: name of a system-wide property
- *title*: title for display elements
- *tooltip text*: text to be displayed as tool tip
- *URI*: identified as such in several methods in org.xml.sax and
  javax.xml methods
- *URL*: identified as such in several methods in javax.swing.
- *XML tag*: element tag in XML


#### Destinations
- *accessibility*: java accessibility objects
- *beans*: java beans properties
- *component retrieval*: retrieval of component based on component name
- *display*: display to the user in a GUI
- *dynamic loading*: string is involved in creating classes to be loaded dynamically
- *field value access*: obtain constant field value by field name
- *logger*: information sent to a logger
- *event handling*: string is used to trigger or notify another component
- *property value*: value of a mapped property
- *property retrieval*: string is used to obtain a mapped value
- *property set*: string is used to map a value
- *reflection*: string is used to retrieve an entity by reflection
- *retrieve content*: string is used to retrieve remove content
- *xml*: XML document handling

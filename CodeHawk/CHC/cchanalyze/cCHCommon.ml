(** {1 Common datatypes and exceptions} 

    {C Copyright 2005-2012; Kestrel Technology LLC; Palo Alto, CA 94304.}  
    
    This program is the unpublished property and trade secret of
    Kestrel Technology. It is to be utilized solely under agreement with
    Kestrel Technology and it is to be maintained on a confidential basis for
    internal company use only. The security and protection of the program is
    paramount to maintenance of the trade secret status. It is to be protected
    from disclosure to unauthorized parties, both within the company party to
    the agreement and outside, in a manner not less stringent than that
    utilized for the company's own proprietary internal information. No copies
    of the Source or Object Code are to leave the premises of the company's
    business except in strict accordance with the agreement signed with Kestrel
    Technology.

    @author Henny Sipma
*)

exception Invocation_error of string
exception Structural_error of string

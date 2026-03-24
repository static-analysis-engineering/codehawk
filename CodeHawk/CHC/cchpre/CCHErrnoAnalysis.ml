open CCHPreTypes

class errno_analysis_digest_t (_fname: string) (_pod: podictionary_int): errno_analysis_digest_int =
object
  method is_active _ = true
  method write_xml _ = ()
  method read_xml _ = Ok()
end
let mk_analysis_digest
      (fname: string)
      (pod: podictionary_int): errno_analysis_digest_int =
  new errno_analysis_digest_t fname pod
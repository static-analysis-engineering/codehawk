class type version_info_int =
  object
    method get_date: string
    method get_description: string
    method get_licensee: string option
    method get_version: string
    method toPretty: CHPretty.pretty_t
  end


class version_info_t :
  ?maxfilesize:int option
  -> ?licensee:string option
  -> version:string
  -> date:string
  -> object
    method get_date: string
    method get_licensee: string option
    method get_maxfilesize: int option
    method get_version: string
    method toPretty: CHPretty.pretty_t
  end


val version: version_info_t

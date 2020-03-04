class version_info_t :
  version:string ->
  date:string ->
  object
    method get_date : string
    method get_version : string
    method toPretty : CHPretty.pretty_t
  end
val version : version_info_t

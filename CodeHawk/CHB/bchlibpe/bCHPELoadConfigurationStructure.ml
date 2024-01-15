(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
   ============================================================================= *)

(* =============================================================================
   The implementation in this file is based on the document:

   Microsoft Portable Executable and Common Object File Format Specification,
   Revision 8.2 - September 21, 2010.
   ============================================================================= *)

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHTraceResult
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper

(* bchlibpe *)
open BCHLibPETypes

module TR = CHTraceResult


let check_tr_result (msg: string) (r: 'a traceresult): 'a =
  if Result.is_ok r then
    TR.tget_ok r
  else
    fail_tvalue
      (trerror_record
         (LBLOCK [
              STR "BCHPELoadConfigurationStructure:";
              STR msg]))
      r


class load_configuration_directory_t:load_configuration_directory_int =
object (self)

  val mutable sectionRVA = wordzero
  val mutable directoryRVA = wordzero

  val mutable characteristics = wordzero
  val mutable timeDateStamp = wordzero
  val mutable majorVersion = 0
  val mutable minorVersion = 0
  val mutable globalFlagsClear = wordzero
  val mutable globalFlagsSet = wordzero
  val mutable criticalSectionDefaultTimeout = wordzero
  val mutable decommitFreeBlockThreshold = wordzero
  val mutable decommitTotalFreeThreshold = wordzero
  val mutable lockPrefixTable = wordzero
  val mutable maximumAllocationSize = wordzero
  val mutable virtualMemoryThreshold = wordzero
  val mutable processAffinityMask = wordzero
  val mutable processHeapFlags = wordzero
  val mutable csdVersion = 0
  val mutable reservedValue = 0
  val mutable editList = wordzero
  val mutable securityCookie = wordzero
  val mutable seHandlerTable = wordzero
  val mutable seHandlerCount = wordzero

  val mutable se_handler_table = Array.make 1 wordzero

  method set_section_RVA (address:doubleword_int) =
    sectionRVA <- address

  method set_directory_RVA (address:doubleword_int) =
    directoryRVA <- address

  method get_SE_handler_table_VA =
    seHandlerTable

  method get_SE_handler_table_size =
    check_tr_result
      "load_configuration_directory#get_SE_handler_table_size"
      (seHandlerCount#multiply_int 4)

  method read (byte_string:string) =
    try
      let offset =
        check_tr_result
          "load_configuration_directory#read offset"
          (directoryRVA#subtract_to_int sectionRVA) in
      let ch = make_pushback_stream (string_suffix byte_string offset) in
      begin
    (* 0, 4, Characteristics ---------------------------------------------------
       Flags that indicate attributes of the file, currently unused.
       ------------------------------------------------------------------------- *)
	characteristics <- ch#read_doubleword;

    (* 4, 4, TimeDateStamp -----------------------------------------------------
       Date and time stamp value.
       ------------------------------------------------------------------------- *)
	timeDateStamp <- ch#read_doubleword;

    (* 8, 2, MajorVersion ------------------------------------------------------
       Major version number.
       ------------------------------------------------------------------------- *)
	majorVersion <- ch#read_ui16;

    (* 10, 2, MinorVersion -----------------------------------------------------
       Minor version number.
       ------------------------------------------------------------------------- *)
	minorVersion <- ch#read_ui16;

    (* 12, 4, GlobalFlagsClear -------------------------------------------------
       The global loader flags to clear for this process as the loader starts the
       process.
       -------------------------------------------------------------------------- *)
	globalFlagsClear <- ch#read_doubleword;

    (* 16, 4, GlobalFlagsSet ---------------------------------------------------
       The global loader flags to set for this process as the loader starts the
       process.
       ------------------------------------------------------------------------- *)
	globalFlagsSet <- ch#read_doubleword;

    (* 20,4, CriticalSectionDefaultTimeout -------------------------------------
       The default timeout value to use for this process's critical sections
       that are abandoned.
       ------------------------------------------------------------------------- *)
	criticalSectionDefaultTimeout <- ch#read_doubleword;

    (* 24, 4, DecommitFreeBlockThreshold ---------------------------------------
       Memory that must be freed before it is returned to the system, in bytes.
       ------------------------------------------------------------------------- *)
	decommitFreeBlockThreshold <- ch#read_doubleword;

    (* 28, 4, DecommitTotalFreeThreshold ---------------------------------------
       Total amount of free memory, in bytes.
       ------------------------------------------------------------------------- *)
	decommitTotalFreeThreshold <- ch#read_doubleword;

    (* 32, 4, LockPrefixTable --------------------------------------------------
       [x86 only] The VA of a list of addresses where the LOCK prefix is used so
       that they can be replaced with NOP on single processes machines.
       ------------------------------------------------------------------------- *)
	lockPrefixTable <- ch#read_doubleword;

    (* 36, 4, MaximumAllocationSize --------------------------------------------
       Maximum allocation size, in bytes.
       ------------------------------------------------------------------------- *)
	maximumAllocationSize <- ch#read_doubleword;

    (* 40, 4, VirtualMemoryThreshold -------------------------------------------
       Maximum virtual memory size, in bytes.
       ------------------------------------------------------------------------- *)
	virtualMemoryThreshold <- ch#read_doubleword;

    (* 44, 4, ProcessAffinityMask ----------------------------------------------
       Setting this field to a non-zero value is equivalent to calling
       SetProcessAffinityMask with this value during process startup (.exe only).
       ------------------------------------------------------------------------- *)
	processAffinityMask <- ch#read_doubleword;

    (* 48, 4, ProcessHeapFlags -------------------------------------------------
       Process heap flags that correspond to the first argument of the
       HeapCreate function. These flags apply to the process heap that is
       created during process startup.
       ------------------------------------------------------------------------- *)
	processHeapFlags <- ch#read_doubleword;

    (* 50, 2, CSDVersion -------------------------------------------------------
       The service pack version identifier.
       ------------------------------------------------------------------------- *)
	csdVersion <- ch#read_ui16;

    (* 52, 2, Reserved ---------------------------------------------------------
       Must be zero.
       ------------------------------------------------------------------------- *)
	reservedValue <- ch#read_ui16;

    (* 56, 4, EditList ---------------------------------------------------------
       Reserved for use by the system.
       ------------------------------------------------------------------------- *)
	editList <- ch#read_doubleword;

    (* 60, 4, SecurityCookie ---------------------------------------------------
       A pointer to a cookie that is used by Visual C++ or GS implementation.
       ------------------------------------------------------------------------- *)
	securityCookie <- ch#read_doubleword;

    (* 64, 4, SEHandlerTable ---------------------------------------------------
       [x86 only] The VA of the sorted table of RVAs of each valid, unique SE
       handler in the image.
       ------------------------------------------------------------------------- *)
	seHandlerTable <- ch#read_doubleword;

    (* 68, 4, SEHandlerCount ---------------------------------------------------
       [x86 only] The count of unique handlers in the table.
       ------------------------------------------------------------------------- *)
	seHandlerCount <- ch#read_doubleword;
      end
    with
    | IO.No_more_input ->
      begin
	ch_error_log#add
          "no more input"
	  (STR "load_configuration_directory#read");
	raise IO.No_more_input
      end
    | Invalid_argument s
    | Invocation_error s ->
      begin
	ch_error_log#add
          "invalid argument"
	  (LBLOCK [STR "load_configuration_directory#read: "; STR s]);
      end

  method read_SE_handler_table (imageBase:doubleword_int) (byte_string:string) =
    try
      let rva =
        check_tr_result
          "load_configuration_directory#read_SE_handler_table rva"
          (seHandlerTable#subtract imageBase) in
      let offset =
        check_tr_result
          "load_configuration_directory#read_SE_handler_table offset"
          (rva#subtract_to_int sectionRVA) in
      if offset < String.length byte_string then
	let ch = make_pushback_stream (string_suffix byte_string offset) in
	let count = seHandlerCount#to_int in
	begin
	  se_handler_table <- Array.make count wordzero;
	  for i=0 to (count-1) do
	    se_handler_table.(i) <- ch#read_doubleword
	  done
	end
      else
	ch_error_log#add
          "PE headers"
	  (LBLOCK [
               STR "Unable to read SE handler table: ";
	       STR "offset: ";
               INT offset;
	       STR "; byte string length: ";
               INT (String.length byte_string)])
    with
    | IO.No_more_input ->
      begin
	ch_error_log#add
          "no more input"
	  (STR "load_configuration_directory_t#read_SE_handler_table");
	raise IO.No_more_input
      end
    | Invalid_argument s ->
      begin
	ch_error_log#add
          "invalid argument"
	  (LBLOCK [
               STR "load_configuration_directory#read_SE_handler_table: ";
               STR s]);
      end

  method get_SE_handlers =
    Array.fold_left (fun a v -> v::a) [] se_handler_table

  method private write_xml_se_handler_table (node:xml_element_int) =
    let append = node#appendChildren in
    Array.iter (fun v ->
      let vNode = xmlElement "se-handler" in
      begin
	vNode#setAttribute "address" v#to_hex_string;
	append [vNode]
      end) se_handler_table

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti t i = if i = 0 then () else node#setIntAttribute t i in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    let sNode = xmlElement "se-handler-table" in
    begin
      self#write_xml_se_handler_table sNode;
      append [sNode];
      setx "characteristics" characteristics;
      setx "timestamp-dw" timeDateStamp;
      set "timestamp" timeDateStamp#to_time_date_string;
      seti "major-version" majorVersion;
      seti "minor-version" minorVersion;
      setx "global-flags-clear" globalFlagsClear;
      setx "global-flags-set" globalFlagsSet;
      setx "critical-section-default-timeout" criticalSectionDefaultTimeout;
      setx "decommit-free-block-threshold" decommitFreeBlockThreshold;
      setx "decommit-total-free-threshold" decommitTotalFreeThreshold;
      setx "lock-prefix-table" lockPrefixTable;
      setx "maximum-allocation-size" maximumAllocationSize;
      setx "virtual-memory-threshold" virtualMemoryThreshold;
      setx "process-affinity-mask" processAffinityMask;
      seti "csd-version" csdVersion;
      seti "reserved" reservedValue;
      setx "edit-list" editList;
      setx "se-handler-table-va" seHandlerTable;
      setx "se-handler-count" seHandlerCount
    end

  method private se_handler_table_to_pretty =
    Array.fold_left
      (fun a v -> LBLOCK [a; NL; STR v#to_hex_string]) (STR "") se_handler_table

  method toPretty =
    LBLOCK [
        STR "Characteristics                  ";
        STR characteristics#to_fixed_length_hex_string;
        NL;
        STR "Time/Date stamp                  ";
        STR timeDateStamp#to_time_date_string;
        NL;
        STR "Major version                    ";
        INT majorVersion;
        NL;
        STR "Minor version                    ";
        INT minorVersion;
        NL;
        STR "Global flags clear               ";
        STR globalFlagsClear#to_fixed_length_hex_string;
        NL;
        STR "Global flags set                 ";
        STR globalFlagsSet#to_fixed_length_hex_string;
        NL;
        STR "Critical section default timeout ";
        STR criticalSectionDefaultTimeout#to_fixed_length_hex_string;
        NL;
        STR "Decommit free block threshold    ";
        STR decommitFreeBlockThreshold#to_fixed_length_hex_string;
        NL;
        STR "Decommit total free threshold    ";
        STR decommitTotalFreeThreshold#to_fixed_length_hex_string;
        NL;
        STR "Lock prefix table                ";
        STR lockPrefixTable#to_fixed_length_hex_string;
        NL;
        STR "Maximum allocation size          ";
        STR maximumAllocationSize#to_fixed_length_hex_string;
        NL;
        STR "Virtual memory threshold         ";
        STR virtualMemoryThreshold#to_fixed_length_hex_string;
        NL;
        STR "Process affinity mask            ";
        STR processAffinityMask#to_fixed_length_hex_string;
        NL;
        STR "Process heap flags               ";
        STR processHeapFlags#to_fixed_length_hex_string;
        NL;
        STR "CSD version                      ";
        INT csdVersion;
        NL;
        STR "Reserved (must be 0)             ";
        INT reservedValue;
        NL;
        STR "Edit list                        ";
        STR editList#to_fixed_length_hex_string;
        NL;
        STR "Security cookie                  ";
        STR securityCookie#to_fixed_length_hex_string;
        NL;
        STR "SEHandler table                  ";
        STR seHandlerTable#to_fixed_length_hex_string;
        NL;
        STR "SEHandler count                  ";
        STR seHandlerCount#to_fixed_length_hex_string;
        NL;
        NL;
        STR "SEHandler table";
        NL; INDENT (5, self#se_handler_table_to_pretty);
        NL;
        NL]

end


let make_load_configuration_directory () = new load_configuration_directory_t

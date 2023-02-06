theory FileSystem
  imports  "Z_Machines.Z_Machine"

begin 
\<comment>\<open>we define the basic types: keys and data for local operations of File, and name for global System\<close>
type_synonym key = integer
type_synonym data = integer
type_synonym name = string

consts
  KEY :: "key set"
  DATA :: "data set"
  NAME :: "name set"

(*shall report be lowercase here? ? ?*)
enumtype report = key_in_use |key_not_in_use | okay | file_exists| file_does_not_exist |file_is_open | file_is_not_open

definition [z_defs]: "Report = {key_in_use,  key_not_in_use, okay, file_exists, file_does_not_exist ,file_is_open , file_is_not_open}"


subsection \<open> Local State Space \<close>
\<comment>\<open>A file should not associate the same key with two different pieces of data, hence the relation 'contents' should be a partial function.\<close>
zstore File =
  contents :: "key \<Zpfun> data"

subsection \<open> Local Operations \<close>

\<comment>\<open>4 Local operations: operation of one file: read, write, add, delete, failtoreadwritedelete, failtoadd\<close>

\<comment>\<open>Read0 /\ Success: A successful read operation requires an existing key k as input and provides the corresponding datum d as output, also reports 'okay':\<close>
zoperation ReadSuccess =
  over File
  params k\<in>KEY d\<in>DATA r\<in>"{okay}"
  pre " k\<in>dom contents \<and> d= contents k"
 
\<comment>\<open>Write0 /\ Success: A successful write operation replaces the datum stored under an existing key k with new input datum d, and provides report output as 'okay'\<close>
zoperation WriteSuccess =
  over File
  params k\<in>KEY d\<in>DATA r\<in>"{okay}"
  pre " k\<in>dom contents "
  update "[contents\<Zprime> = contents \<oplus> {k \<mapsto> d}]"

\<comment>\<open>Add0 /\ Success: a successful add operation adds a new datum d to key k. It has a complementary precondition: the input key k must not be in the domain of contents. It produces a report of 'okay'\<close>
zoperation AddSuccess =
  over File
  params k\<in>KEY d\<in>DATA r\<in>"{okay}"
  pre " k\<notin>dom contents "
  update "[contents\<Zprime> = contents \<oplus> {k \<mapsto> d}]"

\<comment>\<open>Delete0 /\ Success: a successful delete operation requires only that the input key k exists. the state of the file will change:The effect of removing the key is modelled using domain co-restriction: the maplet starting at k is removed from contents.
It also produces a report of 'okay'\<close>
zoperation DeleteSuccess =
  over File
  params k\<in>KEY r\<in>"{okay}"
  pre " k\<in>dom contents "
  update "[contents\<Zprime> = {k} \<Zndres> contents]"

\<comment>\<open>KeyNotInUse: An error may arise because the specified key is not in use, this results in fail to read, write or delete. 
We renamed this operation is same as FailToRWD\<close>
zoperation FailToRWD =
  over File
  params k\<in>KEY r\<in>"{key_not_in_use}"
  pre " k\<notin>dom contents "


\<comment>\<open>KeyInUse: renamed as FailToAdd because it results in fail to add\<close>
zoperation FailToAdd =
  over File
  params k\<in>KEY r\<in>"{key_in_use}"
  pre " k\<in>dom contents "

(*Is it possible to combine success and fail in one operation as in Z? ? ? ? *)


subsection \<open>Local zmachine \<close>

def_consts
KEY = "{1,2,3}"
DATA = "{100,101}"
(*? ? ?  {1..5} fail*)

(* there can be only one Init in a thy file?
 Init is a keyword and can not renamed as FileInit? ? 
definition Init :: "File subst" where
  [z_defs]:
  "Init = 
   [contents\<Zprime> = {\<mapsto>}
   ]"
*)
zmachine FileProc =
  over File
  init "[contents\<Zprime> = {\<mapsto>}  ]"
  operations ReadSuccess WriteSuccess AddSuccess 
DeleteSuccess FailToRWD FailToAdd
\<comment>\<open>When a file is initialised in 'init', it contains no data, so the value of 'contents' should be the empty function.\<close>


(*animate FileProc *)

subsection \<open> Global state space \<close>
\<comment>\<open>A file system contains a number of files indexed using a set of names.
files is the collection of named files known to the system.
opened is the set of files that are currently open.
It is important that the system should not associate the same name with two different files: files must always be functional\<close>
zstore System =
  "files" :: "name \<Zpfun> File"
  "opened" :: "name set"
  where " opened \<subseteq> dom files "
(*file and open are keywords, "" does not work in where section, so change file to files, open to opened*)


subsection \<open> Global operations, no local operation involved\<close>

\<comment>\<open>Open0 /\ Success: A successful open operation adds a name n to the list of open files, and report 'okay'.
An open operation will fail if the input name n  denotes a file that is already open.\<close>
zoperation OpenSuccess =
  over System
  params n\<in>NAME r\<in>"{okay}"
  pre " n\<in>dom files \<and>  n\<notin> opened"
  update "[opened\<Zprime> = opened \<union> {n}]"

\<comment>\<open>Close0 /\ Success : A successful close operation removes a name n from the list of open files.
A close operation will fail if the input name n does not denote an open file.\<close>
zoperation CloseSuccess =
  over System
  params n\<in>NAME r\<in>"{okay}"
  pre " n\<in>dom files \<and>  n\<in> opened"
  update "[opened\<Zprime> = opened - {n}]"


\<comment>\<open>Create0 /\ Success : A successful create operation adds a new name n to the list of files known to the system.
the state of the file associated with name n
is described by the Init of File\<close>
zoperation CreateSuccess =
  over System
  params n\<in>NAME r\<in>"{okay}"
  pre " n \<notin> dom files"
  update "[files\<Zprime> = files \<oplus> {n \<mapsto> \<lblot> contents \<leadsto> {\<mapsto>} \<rblot>}]"

\<comment>\<open>Destroy0 /\ Success: A successful destroy operation removes a name from the list of files, do-
main co-restricting the function files\<close>
zoperation DestroySuccess =
  over System
  params n\<in>NAME r\<in>"{okay}"
  pre "n\<notin>opened \<and>  n \<in> dom files "
  update "[files\<Zprime> = {n} \<Zndres> files]"
(*We wish to insist that input n is not an element of open, thus preventing the destruction of open files. in Z operation FileManage invariant 'opened\<Zprime>= opened' guarantee that we can only destroy a closed file, but in ZM it is not enough to have ' opened\<Zprime>= opened' in update, because in the System invariant opened \<subseteq> dom files assures if we cannot remove n from open, then we cannot remove n from the domain of files. 
But in ZM, we need 'n\<notin>opened' as an explicit precondition*)


subsection \<open>Global report operations, , no local operation involved\<close>

\<comment>\<open>If we attempt to create a file using a name that is already in use, we will receive a report complaining that a file with that name exists\<close>
zoperation FileExists =
  over System
  params n\<in>NAME r\<in>"{file_exists}"
  pre " n \<in> dom files"

\<comment>\<open>if we attempt to destroy a file using a name that is not in use, we will receive a report complaining that the file does not exist\<close>
zoperation FileDoesNotExists =
  over System
  params n\<in>NAME r\<in>"{file_does_not_exist}"
  pre " n \<notin> dom files"

\<comment>\<open>Sometimes a file will be open when it should be closed\<close>
zoperation FileIsOpen =
  over System
  params n\<in>NAME r\<in>"{file_is_open}"
  pre " n \<in> opened"

\<comment>\<open>sometimes a file will be closed when it should be open\<close>
zoperation FileIsNotOpen =
  over System
  params n\<in>NAME r\<in>"{file_is_not_open}"
  pre " n \<in> dom files \<and> n\<notin> opened"

(*? ? ? can not link the report operation to the specific operation failure, e.g., OpenFail, CloseFail, etc.*)



subsection \<open> Global operations  Promoted from Local operations on one file\<close>

\<comment>\<open>if the file exists and is open (i.e., n\<in>opened), then the four operations are successful: read write add delete\<close>

zoperation KeyRead0Success =
  over System
  params n\<in>NAME  k\<in>KEY d\<in>DATA r\<in>"{okay}"
  pre "n\<in>opened \<and> k\<in> dom($files[n]:contents) \<and> d= ($files[n]:contents) k"
 (*one precondition is needed: n\<in>dom files, 
Otherwise Animator Fails:
Simulation: undefined CallStack (from HasCallStack):
  error, called at ./Partial_Fun.hs:59:10 in main:Partial_Fun
Same for the following 5 operations*)

zoperation KeyWrite0Success =
  over System
  params n\<in>NAME  k\<in>KEY d\<in>DATA r\<in>"{okay}"
  pre " n\<in>opened \<and> k\<in> dom($files[n]:contents) "
  update "[files[n]:contents\<Zprime> = $files[n]:contents \<oplus> {k \<mapsto> d}]"


zoperation KeyAdd0Success =
  over System
  params n\<in>NAME k\<in>KEY d\<in>DATA r\<in>"{okay}"
  pre "n\<in>opened \<and>  k\<notin> dom($files[n]:contents) "
  update "[files[n]:contents\<Zprime> = $files[n]:contents \<oplus> {k \<mapsto> d}]"


zoperation KeyDelete0Success =
  over System
  params n\<in>NAME k\<in>KEY r\<in>"{okay}"
  pre "n\<in>opened \<and>  k\<in>dom($files[n]:contents) "
  update "[files[n]:contents\<Zprime> = {k} \<Zndres> $files[n]:contents]"



\<comment>\<open>the following 2 Report operation is due to status of the key in the file\<close>

\<comment>\<open>fail to read, write or delete\<close>
zoperation KeyFailToRWD0 =
  over System
  params n\<in>NAME k\<in>KEY r\<in>"{key_not_in_use}"
  pre "n\<in>opened \<and>  k\<notin>dom($files[n]:contents) "


\<comment>\<open>fail to add\<close>
zoperation KeyFailToAdd0 =
  over System
  params n\<in>NAME  k\<in>KEY r\<in>"{key_in_use}"
  pre "n\<in>opened \<and>  k\<in>dom($files[n]:contents) "



\<comment>\<open>the following ? Report operation is due to status of the file\<close>
(*these 2 are the same as FileIsNotOpen and FileDoesNotExists, still no way to link the report to a specific file management operation *)
zoperation FileFailureDueToFileIsNotOpen =
  over System
  params n\<in>NAME r\<in>"{file_is_not_open}"
  pre " n \<in> dom files \<and> n\<notin> opened"

zoperation FileFailureDueToFileDoesNotExists =
  over System
  params n\<in>NAME r\<in>"{file_does_not_exist}"
  pre " n \<notin> dom files"


\<comment>\<open>When the file system is initialised, there are no files.\<close>
definition Init :: "System subst" where
  [z_defs]:
  "Init = 
   [files\<Zprime> = {'''' \<mapsto> \<lblot> contents \<leadsto> {\<mapsto>} \<rblot>},
  opened\<Zprime> = {}
   ]"
(*files\<Zprime> = { \<mapsto> },why not work? ? ?  *)


subsection \<open> Structural Invariants \<close>

lemma Init_inv[hoare_lemmas]: "Init establishes System_inv"
  by (zpog_full; auto)

lemma OpenSuccess_inv[hoare_lemmas]: "OpenSuccess(n, r) preserves System_inv"
  by (zpog_full)


lemma CloseSuccess_inv[hoare_lemmas]: "CloseSuccess(n, r) preserves System_inv"
  by (zpog_full; auto)


lemma CreateSuccess_inv[hoare_lemmas]: "CreateSuccess(n, r) preserves System_inv"
  by (zpog_full; auto)

lemma DestroySuccess_inv[hoare_lemmas]: "DestroySuccess(n, r) preserves System_inv"
  by (zpog_full; auto)

lemma FileExists_inv[hoare_lemmas]: "FileExists(n, r) preserves System_inv"
  by (zpog_full; auto)

lemma FileDoesNotExists_inv[hoare_lemmas]: "FileDoesNotExists(n, r) preserves System_inv"
  by (zpog_full; auto)

lemma FileIsOpen_inv[hoare_lemmas]: "FileIsOpen(n, r) preserves System_inv"
  by (zpog_full; auto)

lemma FileIsNotOpen_inv[hoare_lemmas]: "FileIsNotOpen(n, r) preserves System_inv"
  by (zpog_full; auto)

lemma KeyRead0Success_inv[hoare_lemmas]: "KeyRead0Success(n,k, d, r) preserves System_inv"
  by (zpog_full; auto)

lemma KeyWrite0Success_inv[hoare_lemmas]: "KeyWrite0Success(n,k, d, r) preserves System_inv"
  by (zpog_full; auto)

lemma KeyAdd0Success_inv[hoare_lemmas]: "KeyAdd0Success(n,k, d, r) preserves System_inv"
  by (zpog_full; auto)

lemma KeyDelete0Success_inv[hoare_lemmas]: "KeyDelete0Success(n,k, r) preserves System_inv"
  by (zpog_full; auto)


lemma KeyFailToRWD0_inv[hoare_lemmas]: "KeyFailToRWD0(n,k, r) preserves System_inv"
  by (zpog_full; auto)


lemma KeyFailToAdd0_inv[hoare_lemmas]: "KeyFailToAdd0(n,k, r) preserves System_inv"
  by (zpog_full; auto)


lemma FileFailureDueToFileIsNotOpen_inv[hoare_lemmas]: "FileFailureDueToFileIsNotOpen(n, r) preserves System_inv"
  by (zpog_full; auto)


lemma FileFailureDueToFileDoesNotExists_inv[hoare_lemmas]: "FileFailureDueToFileDoesNotExists(n, r) preserves System_inv"
  by (zpog_full; auto)


def_consts
NAME = "{''a'',''b'',''c''}"


zmachine SystemProc =
  over System
  init Init
  operations OpenSuccess CloseSuccess CreateSuccess DestroySuccess FileExists FileDoesNotExists FileIsOpen FileIsNotOpen KeyRead0Success KeyWrite0Success KeyAdd0Success KeyDelete0Success KeyFailToRWD0 KeyFailToAdd0

animate SystemProc
 
end
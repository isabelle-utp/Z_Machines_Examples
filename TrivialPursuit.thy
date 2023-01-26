theory TrivialPursuit
  imports "Z_Machines.Z_Machine"
begin

enumtype Player = fang | jim | simon

definition "Player = {fang, jim, simon}"

enumtype Colour = blue | pink | yellow | brown | green | orange

definition Colour :: "Colour set" where
"Colour = {blue, pink, yellow, brown, green, orange}"

zstore LocalScore =
  s :: "Colour set"

zstore GlobalScore =
  score :: "Player \<Zpfun> LocalScore"

zoperation AnswerLocal =
  params c \<in> Colour
  pre "c \<notin> s" 
  update "[s \<leadsto> s \<union> {c}]"

(*
zoperation AnswerGlobal = 
  over GlobalScore
  params p\<in>Player 
  promote AnswerLocal with score[p]
*)

zoperation AnswerGlobal =
  over GlobalScore
  params p\<in>Player c\<in>Colour
  pre "c \<notin> $score[p]:s"
  update "[score[p]:s\<Zprime> = $score[p]:s \<union> {c}]"

zmachine LocalTP =
  over LocalScore
  init "[s\<Zprime> = {}]"
  operations AnswerLocal

zmachine GlobalTP =
  over GlobalScore
  init "[score\<Zprime> = {fang \<mapsto> default, jim \<mapsto> default, simon \<mapsto> default}]"
  operations AnswerGlobal

animate GlobalTP

end
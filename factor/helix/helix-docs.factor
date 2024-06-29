USING: definitions editors help help.markup help.syntax
io io.files io.pathnames words ;
IN: editors.helix

ABOUT: "editors.helix"

ARTICLE: "editors.helix" "Helix in Zellij support"
"The " { $link helix-path } " variable contains the name of the zellij executable. The default " { $link helix-path } " is " { $snippet "\"helix\"" } ". If it is found in path, run as `{$link helix-path} -ic -- hx file:linenum`"
{ $list }
$nl
{ $see-also "editor" }
;

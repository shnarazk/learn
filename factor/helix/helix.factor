USING: editors io.standard-paths kernel make math.parser
namespaces sequences strings ;
IN: editors.helix

SINGLETON: helix

MIXIN: helix-base

INSTANCE: helix helix-base

SYMBOL: helix-path

HOOK: find-helix-path editor-class ( -- path )

HOOK: helix-ui? editor-class ( -- ? )

SYMBOL: helix-tabs?

M: helix-base helix-ui? f ;

M: helix-base find-helix-path "zellij" ?find-in-path ;

: actual-helix-path ( -- path )
    \ helix-path get [ find-helix-path ] unless* ;

! zellij run --floating -- zsh -ic "hx ."

M: helix-base editor-command
    [
        actual-helix-path dup string? [ , ] [ % ] if
        "run" , "-c" , "--" , "hx" ,
        number>string ":" prepend append ,
    ] { } make ;

M: helix-base editor-detached? f ;

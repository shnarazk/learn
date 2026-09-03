module

public import VersoManual
public import Journal

public section

open Verso.Genre Manual

def config : RenderConfig where
  -- extraFiles := [("static", "static")]
  extraCss := [
    "
.hl.lean {
  background-color: #fefefe; padding: 0.5em; border: solid 1px #bbf;
}
pre {
  background-color: #f8f8f8; padding: 0.5em; border: solid 1px #99e;
}
img {
  max-width: 100%;
}
"
  ]

def main := manualMain (%doc Journal) (config := config)

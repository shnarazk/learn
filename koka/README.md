# Learning 効果

### Helix setting for one of VScode-oriented languages

```toml
[language-server.koka]
command = "koka"
args = ["--language-server", "--lsstdio"] # since 3.1.0

[[language]]
name = "koka"
scope = "source.koka"
injection-regex = "koka"
file-types = ["kk"]
# auto-format = true
comment-token = "!"
language-servers = [ "koka" ]
indent = { tab-width = 2, unit = "  " }
shebangs = ["koka"]

[language.auto-pairs]
'(' = ')'
'{' = '}'
'[' = ']'
'"' = '"'

[[grammar]]
name = "koka"
source.git = "https://github.com/mtoohey31/tree-sitter-koka"
source.rev = "96d070c3700692858035f3524cc0ad944cef2594"
```

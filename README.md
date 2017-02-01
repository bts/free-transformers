*UPDATE*: I've worked this into a library in a private project, that abstracts over `Free` and CPS'd `F` for efficiency. If you'd be interested in using this, let me know and I can release a package.

----------------------

An example Haskell implementation of the
"[free transformers](http://degoes.net/articles/modern-fp-part-2)" approach to
building modular programs by composing layers of `Free` interpreters.

This was adapted from a combination of:
- http://mpickering.github.io/posts/2014-12-20-closed-type-family-data-types.html
- http://degoes.net/articles/modern-fp
- http://degoes.net/articles/modern-fp-part-2
- https://github.com/notxcain/onion-architecure
- https://gist.github.com/jdegoes/97459c0045f373f4eaf126998d8f65dc

In this example, the code does not (yet) go so far as to abstract over the
"computational context" (i.e. sequential/`Free` vs parallel/`FreeAp`) --
everything is currently sequential.

If you have any tips/ideas/fixes, please let me know!

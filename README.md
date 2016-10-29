An example implementation of "[free transformers](http://degoes.net/articles/modern-fp-part-2)" in Haskell.

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

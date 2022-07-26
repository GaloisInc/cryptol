# Literal Sampling



## TODO

- [x] remove use of vector-sized and related dependencies -- its not worth it now that I have a good idea of what I'm doing
  - this will require explicit nVars included in some places probably
- [x] make sure to use the `SamplingM` monad basically everywhere -- so that you can reasonably throw errors without causing a crash
- [ ] where to call `sample` from, so I know what type exactly it should have?
# Shell api

Shelling out to z3 instead of linking is the UNIX "api". For multiple query rounds this entails setting up pipes in both directions.

TODO:

* Benchmark optimal pipe buffer sizes.

* Add unsupported languages. Particuarly a C FFI for the rust, Ruby, and Go.

* Benchmark the optimal number of z3 instances for large numbers of cores.

* Add polling so each z3 intance is saturated with K queries.

* Add "serverless" shell workers to run z3 on thousands of instances, https://blog.nelhage.com/post/distributed-builds-for-everyone/ . For AWS Lambda the z3 shell binary can be addded as a "layer" without modification. 





This server provides a subset of the methods that are available in
cryptol-remote-api. It's reason for being is that it does not provide
any commands that allow modifications to the server state (the
provided Cryptol code must be specified in a command-line
argument). This means that it can be used in situations with load
balancing between multiple instances.

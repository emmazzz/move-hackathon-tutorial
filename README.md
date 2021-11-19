# move-hackathon-tutorial
Move tutorial for the hackathon happening on Dec 7-8

### Step 0
- Run the setup script to install Move CLI, Shuffle and dependencies:

```
$ sh step_0/setup.sh
```
- Include environment variable definitions in `~/.profile` by running this command:
```
$ . ~/.profile
```

Once this is done, you can alias the `move` package command to to `mpm`:

```bash
$ alias mpm = "<path_to_diem_repo>/target/debug/df-cli package"
$ alias shuffle = "<path_to_diem_repo>/target/debug/shuffle"
```

You can check that it is working by running `mpm -h`. You should see
something like this along with a list and description of a number of
commands:

```
move-package 0.1.0
Package and build system for Move code.

USAGE:
    move package [FLAGS] [OPTIONS] <SUBCOMMAND>
...
```

There is official Move support for VSCode, you can install this extension
by opening VSCode and searching for the "move-analyzer" package and
installing it. Detailed instructions can be found
[here](https://github.com/diem/diem/tree/main/language/move-analyzer/editors/code).

### Step 1: Write my first Move module

To create your first Move module, we first need to create a Move package by
calling

```
$ mpm new <pkg_name>
```

Now change directory into the package you just created

```
$ cd <pkg_name>
```

and look around. You should see a directory called `sources` -- this is the
place where all the Move code for this package will live[1]. You should
also see a `Move.toml` file which specifies dependencies and other
information about this package, we'll explore this in a bit. If you're
familiar with Rust and Cargo, the `Move.toml` file is similar to the
`Cargo.toml` file, and the `sources` directory similar to the `src`
directory.

Let's write some code! Open up `sources/FirstModule.move` in your
editor of choice.

Modules are the building block of Move code, and they always are defined
relative to a specific address -- the address that they can be published
under. So let's start out by defining our first module, and look at the
different parts:

```rust
module NamedAddr::Coin {
}
```

This is defining the module `Coin` that can be published under the [named
address](https://diem.github.io/move/address.html#named-addresses)
`NamedAddNamedAddr`. Named addresses are a way to parametrize the source
code, so that we can compile this module using different values for
`NamedAddr` to get different bytecode.

Let's now define and assign the named address `NamedAddr` the value `0xDEADBEEF`.
We can do this by opening the `Move.toml` in your favorite editor and adding the
following:

```
[addresses]
NamedAddr = "0xDEADBEEF"
```

Let's now see if it works!

```
$ mpm build
```

Let's now define a structure in this module to represent a `Coin` with a
given `value`:

```
module NamedAddr::Coin {
    struct Coin has key {
        value: u64,
    }
}
```

Structures in Move can be given different
[abilities](https://diem.github.io/move/abilities.html) that describe what
can be done with that type. There are four different abilities in Move:
* `copy`: Allows values of types with this ability to be copied.
* `drop`: Allows values of types with this ability to be popped/dropped.
* `store`: Allows values of types with this ability to exist inside a struct in global storage.
* `key`: Allows the type to serve as a key for global storage operations.

So in this module we are saying that the `Coin` struct can be used as a key
in global storage, and because it has no other abilites, it cannot be
copied, dropped, or stored as a non-key value in storage.

We can then add some functions to this module, functions are default
private, and can also be `public`, or `public(script)`. The latter states
that this function can be called from a transaction script.
`public(script)` functions can also be called by other `public(script)`
functions.

Let's check that it can build again

```
$ mpm build
```

Let's now add a function that mints coins and stores them under an
account:

```
module NamedAddr::Coin {
    struct Coin has key {
        value: u64,
    }

    public fun mint(account: signer, value: u64) {
        move_to(&account, Coin { value })
    }
}
```

Let's take a look at this function and what it's saying:
* It takes a [`signer`](https://diem.github.io/move/signer.html) -- an
  unforgeable token that represents control over a particular address, and
  a `value` to mint.
* It creates a `Coin` with the given value and stores it under the
  `account` using one of the [five different global storage
  operators](https://diem.github.io/move/global-storage-operators.html)
  `move_to`. This is where the `key` ability is imporant -- we couldn't
  call `move_to` on `Coin` unless it had the `key` ability!

Let's make sure it compiles now:

```
$ mpm build
```

### Step 2: Add unit tests to my first Move module

Now that we've written our first Move module, lets

#### Adding dependencies

#### Exercise?
* Implement withdraw and deposit and add tests for them

### Step 3: Design my ERC20 module

### Step 4: Implement my ERC20 module

### Step 5: Add unit tests to my ERC20 module

### Step 6: Make my ERC20 module generic

## Advanced steps

### Step 7: Write formal specifications for my ERC20 module

### Step 8: Formally verify my ERC20 module using Move Prover


Footnotes
---------------------------------------------------------------------------
[1] Move code can also live a number of other places, but for more
information on that see the [documentation on Move
packages](https://diem.github.io/move/packages.html).

Notes (to be removed in final version):
---------------------------------------------------------------------------
* We should base things on the assumption that these steps will be run in
  the Diem repo at the end.

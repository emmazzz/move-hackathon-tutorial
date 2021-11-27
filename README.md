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

### Step 3: Design my BasicCoin module

In this section, we are going to design a module implementing a basic coin and balance interface, where coins can
be minted and transferred between balances under different addresses.

The signatures of the public Move function are the following:

```
public fun balance_of(owner: address): u64 acquires Balance;
public(script) fun transfer(from: signer, to: address, amount: u64) acquires Balance;
```
At the end of each function signature is an `acquires` list containing all the resources defined in this module accessed by the function.

Notice that `balance_of` is a public function while `transfer` is a _public script_ function.
Similar to Ethereum, users submit signed transactions to Move-powered blockchains to update the blockchain state. 
We can invoke `transfer` method in a transaction script to modify the blockchain state. As mentioned in Step 1, only public script 
functions can be called from a transaction script. Therefore, we declare `transfer` as a public script function. 
And by requiring the `from` argument be a `signer` instead of an `address`, we require that the transfer transaction
must be signed by the `from` account.

Next we look at the data structs we need for this module. 

In most Ethereum contracts, the balance of each address is stored in a _state variable_ of type 
`mapping(address => uint256)`. This state variable is stored in the storage of a particular smart contract. In Move, however, storage
works differently. A Move module doesn't have its own storage. Instead, Move "global storage" (what we call our
blockchain state) is indexed by addresses. Under each address there are Move modules (code) and Move resources (values).

The global storage looks roughly like

```
struct GlobalStorage {
    resources: Map<address, Map<ResourceType, ResourceValue>>
    modules: Map<address, Map<ModuleName, ModuleBytecode>>
}
```

The Move resource storage under each address is a map from types to values. (An observant reader might observe that
this means each address can only have one value of each type.) This conveniently provides us a native mapping indexed
by addresses. In our BasicCoin module, we define the following `Balance` resource representing the number of coins 
each address holds:

```
/// Struct representing the balance of each address.
struct Balance has key {
    coin: Coin // same Coin from Step 1
}
```

## TODO: change the diagrams to get rid of total supply 

Roughly the Move blockchain state should look like this:
![](diagrams/move_state.png)
In comparison, a Solidity blockchain state might look like this:
![](diagrams/solidity_state.png)

### Step 4: Implement my BasicCoin module

We have created a Move package for you in folder `step_4` called `BasicCoin`. `sources` folder contains source code for 
all your Move modules. `BasicCoin.move` lives inside this folder. In this section, we will take a closer look at the 
implementation of the methods inside `BasicCoin.move`.

#### Method `initialize`

Unlike Solidity, Move doesn't have a built-in `constructor` method called at the instantiation of the smart contract. 
We can, however, define our own initializer that can only be called by the module owner. We enforce this using the  
assert statement:
```
assert!(Signer::address_of(&module_owner) == MODULE_OWNER, ENOT_MODULE_OWNER);
```
Assert statements in Move can be used in this way: `assert!(<predicate>, <abort_code>);`. This means that if the `<predicate>`
is false, then abort the transaction with `<abort_code>`. Here `MODULE_OWNER` and `ENOT_MODULE_OWNER` are both constants 
defined at the beginning of the module.

We then perform two operations in this method:
1. Publish an empty `Balance` resource under the module owner's address.
2. Deposit a coin with value `total_supply` to the newly created balance of the module owner.

#### Method `balance_of`

Similar to `total_supply`, we use `borrow_global`, one of the global storage operators, to read from the global storage.
```
borrow_global<Balance>(owner).coin.value
                 |       |       \    /
        resource type  address  field names
```

#### Method `transfer`
This function withdraws tokens from `from`'s balance and deposits the tokens into `to`s balance. We take a closer look 
at `withdraw` helper function:
```
fun withdraw(addr: address, amount: u64) : Coin acquires Balance {
    let balance = balance_of(addr);
    assert!(balance >= amount, EINSUFFICIENT_BALANCE);
    let balance_ref = &mut borrow_global_mut<Balance>(addr).coin.value;
    *balance_ref = balance - amount;
    Coin { value: amount }
}
```
At the beginning of the method, we assert that the withdrawing account has enough balance. We then use `borrow_global_mut` 
to get a mutable reference to the global storage, and `&mut` is used to create a [mutable reference](https://diem.github.io/move/references.html) to a field of a 
struct. We then modify the balance through this mutable reference and return a new coin with the withdrawn amount. 
 

### Compiling our code 

Now that we have implemented our BasicCoin contract, let's try building it using Move package by running the following command 
in `step_4/BasicCoin` folder:
```
$ mpm build
```

### Exercises
There is a `TODO` in our module, left as an exercise for the reader:
- Implement `deposit` method.

The solution to this exercise can be found in `step_4_sol`.

**Bonus exercises**
- What would happen if we deposit too many tokens to a balance?
- Is the initializer guaranteed to be called before anything else? If not, how can we 
change the code to provide this guarantee?

### Step 5: Add unit tests to my BasicCoin module

### Step 6: Make my BasicCoin module generic

In Move, we can use generics to define functions and structs over different input data types. Generics are a great 
building block for library code. In this section, we are going to make our simple Coin module generic so that it can 
serve as a library module that can be used by other user modules.

First, we add type parameters to our data structs:
```
struct Coin<phantom CoinType> has store {
    value: u64
}

struct Balance<phantom CoinType> has key {
    coin: Coin<CoinType>
}
```

Here we declare the type parameter `CoinType` to be _phantom_ because `CoinType` is not used in the struct definition 
or is only used as a phantom type parameter. There are ability constraints you can add to a type parameter to require
that the type parameter has certain abilities, like `T: copy + drop`. Read more about 
[generic](https://diem.github.io/move/generics.html) here.

We also add type parameters to our methods in the same manner. For example, `withdraw` becomes the following:
```
fun withdraw<CoinType>(addr: address, amount: u64) : Coin<CoinType> acquires Balance {
    let balance = balance_of<CoinType>(addr);
    assert!(balance >= amount, EINSUFFICIENT_BALANCE);
    let balance_ref = &mut borrow_global_mut<Balance<CoinType>>(addr).coin.value;
    *balance_ref = balance - amount;
    Coin<CoinType> { value: amount }
}
```
Take a look at `step_6/BasicCoin/sources/BasicCoin.move` to see the full implementation.

At this point, readers who are familiar with Ethereum might notice that this module serves a similar purpose as 
the [ERC20 token standard](https://ethereum.org/en/developers/docs/standards/tokens/erc-20/), which provides an 
interface for implementing fungible tokens in smart contracts. One key advantage of using generics is the ability
to reuse code since the generic library module already provides a standard implementation and the instantiation module
can provide customizations by wrapping the standard implementation. We provide a little module that instantiates 
the Coin type and customizes its transfer policy: only odd number of coins can be transferred. 


## Advanced steps

### Step 7: Write formal specifications for my BasicCoin module

### Step 8: Formally verify my BasicCoin module using Move Prover


Footnotes
---------------------------------------------------------------------------
[1] Move code can also live a number of other places, but for more
information on that see the [documentation on Move
packages](https://diem.github.io/move/packages.html).

Notes (to be removed in final version):
---------------------------------------------------------------------------
* We should base things on the assumption that these steps will be run in
  the Diem repo at the end.

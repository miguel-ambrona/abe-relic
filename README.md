# Attribute-Based Encryption (Relic)

## Installation

*1*. Install [Opam](https://opam.ocaml.org/).

 * In Ubuntu,

~~~~~
apt-get install -y ocaml ocaml-native-compilers opam m4 camlp4-extra
~~~~~

 * In OS X, use homebrew,

~~~~~
brew install opam
~~~~~

*2*. Install Relic:

To install relic, clone the repository from https://github.com/relic-toolkit/relic and follow the instructions below:

~~~~~
mkdir build
cd build
cmake build --ALLOC=DYNAMIC --SHLIB=on ../
~~~~~

The flag --ALLOC=DYNAMIC may not work. Check that the file include/relic_conf.h contains the line "#define ALLOC   DYNAMIC" and fix it if necessary.

~~~~~
make
sudo make install
~~~~~

The installation works for commit 0e239a842b89126080e998e3836f83aff1078576 of relic.

*3*. Install the Ocaml Bindings for Relic:

Install opam packages:

~~~~~
git clone https://github.com/ZooCrypt/relic-ocaml-bindings.git
opam pin add relic-ocaml-bindings RELIC_OCAML_BINDINGS_DIR -n
opam install relic-ocaml-bindings --deps-only
~~~~~

Compile and install the bindings:

~~~~~
oasis setup
./configure
make
opam install relic-ocaml-bindings
~~~~~

*4*. To compile and test our ABE implementation from Relic, execute the following commands:

~~~~~
make
./test_abe.native
~~~~~

## Usage (Batch mode)

The tool supports four modes (corresponding to the four ABE algorithms) given as first argument:

- setup: this algorithm gets as input the public parameters (security parameter, attribute universe,
  predicate universe...) and outputs the master public key (mpk) and the master secret key (msk).

- encrypt: the encryption algorithm takes as input the master public key (mpk), a message and a value
  *x* (corresponding to a *set of attributes* in KP-ABE or a *policy* in CP-ABE) and outputs a ciphertext
  *ct_x*.

- keygen: the key generation algorithm gets as input mpk and msk and a value *y* (corresponding to a *poliy* in
  KP-ABE or a *set of attributes* in CP-ABE) and outputs a secret key *sk_y*.
  Note that this algorithm needs the msk as input and thus, it is not a public algorithm. It
  is supposed to be runned by the master authority of the system.

- decrypt: the decryption algorithm takes as input *sk_y* and *ct_x* and outputs a message. It will
  succeed if and only if x and y are such that the *policy* is satisfied by the *set of attributes*.

### Example

We set the file *public_parameters.txt* as:

~~~~
scheme = CP_ABE.
predicate = boolean_formula(2 repetitions, 4 and-gates).
attributes = [tall, dark, handsome, phd, cs, maths].
~~~~

We run the algorithm:

~~~~
$ ./abe_relic.native setup -pp public_parameters.txt -mpk mpk.txt -msk msk.txt
~~~~

This will produce two files, *mpk.txt* and *msk.txt*, containing the information of the master public
key and the master secret key respectively.

We will encrypt the message in file *message.txt* containing:

~~~~
L'essentiel est invisible pour les yeux
~~~~

For this, we run the encryption algorithm:

~~~~
$ ./abe_relic.native encrypt -mpk mpk.txt -msg message.txt -out ciphertext.txt \
                   -policy "(tall and handsome and dark) or (phd and cs)"
~~~~

Only users with a secret key satisfying the policy will be able to decrypt. As an example, we
create two secret keys corresponding to different attributes:

~~~~
$ ./abe_relic.native keygen -mpk mpk.txt -msk msk.txt -out key1.txt -attrs "[phd, cs]"
$ ./abe_relic.native keygen -mpk mpk.txt -msk msk.txt -out key2.txt -attrs "[tall, dark, phd, maths]"
~~~~

Decryption will succeed only for the first key:

~~~~
$ ./abe_relic.native decrypt -mpk mpk.txt -ct ciphertext.txt -sk key1.txt
L'essentiel est invisible pour les yeux
~~~~

~~~~
$ ./abe_relic.native decrypt -mpk mpk.txt -ct ciphertext.txt -sk key2.txt
bad decrypt
~~~~


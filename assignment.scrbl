#lang scribble/manual
@require[scribble-math]
@require[scribble-math/dollar]
@require[racket/runtime-path]

@require["../../lib.rkt"]
@define-runtime-path[hw-file "hw7.lean"]


@title[#:tag "hw7" #:style (with-html5 manual-doc-style)]{Homework 7}

@bold{Released:} @italic{Wednesday, February 22, 2023 at 6:00pm}

@bold{Due:} @italic{Thursday, March 2, 2023 at 6:00pm}

@nested[#:style "boxed"]{
What to Download:

@url{https://github.com/logiccomp/s23-hw7/raw/main/hw7.lean}
}

Please start with this file, filling in where appropriate, and submit your homework to the @tt{hw7} assignment on Gradescope. This page has additional information, and allows us to format things nicely.

@bold{To do this assignment in the browser: @link["https://github.com/codespaces/new?machine=basicLinux32gb&repo=578247545&ref=main&devcontainer_path=.devcontainer%2Fdevcontainer.json&location=EastUs"]{Create a Codespace}.}

@larger{Your overall task} In this assignment, there are many theorems that have @lean{sorry} as their proof. Your goal is to replace those with other tactics that complete the proof. If you are unable to complete a proof, you can always give up at any point with @lean{sorry}, leaving whatever in-progress state you had. 

@section{Problem 1: Redoing proofs with tactics}

In this first section, you'll redo proofs you did in HW5, this time using tactics you have learned. Try to avoid using @lean{exact}, or if you must use it, use it on small terms, rather than large terms that replicate what you did in HW5.

@minted-file-part["lean" "p1" hw-file]

@section{Problem 2: More complex logical proofs}
In this problem, you'll tackle a few more complex logical equivalences.

@minted-file-part["lean" "p2" hw-file]


@section{Problem 3: Induction on numbers and lists}

Finally, you'll do a few proofs that will likely require induction. Note that this entire assignment @italic{redefines} the built in types @lean{Nat} and @lean{List}, and redefines many of the operations on them. The reason for doing that is the standard library has some automation that can get in the way of our proofs, at least to start. This way, all of the definitions used are readily available: it does mean that, for example, the special infix syntax for @lean{List}s is not available (as that is only for the built in ones).

When approaching inductive proofs, remember that it can be very tempting to "do induction again". That's _rarely_ the right solution: usually, the answer is actually to start more generally (and perform induction before you have introduced any extra variables into the context, so that your inductive hypothesis is as strong as possible).

In these proofs, to help keep you within the rails, we've provided line counts for our reference proofs. We certainly don't expect you to have the exact same numbers (and lines are a pretty poor metric of code), but if you see that we did a proof in 5 lines, and you're at 50, it's a good indication that maybe you should reconsider your approach. On the other hand, if we had 10, and you have 15, there is no reason to think you did anything wrong! And of course, if we did something in 8 that you did in 4, that is also fine! 

@minted-file-part["lean" "p3" hw-file]

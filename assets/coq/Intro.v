(* Explorations of Coq fundamentals *)

(* There are many great resources and tutorials for beginners to build basic skills in using 
   Coq. I myself started with Pierce's Software Foundations, and I highly recommend others do 
   the same.
   
   At a certain point however, once the beginner finds themselves comfortable with the basic 
   assortment of tools provided by Coq, they may start to wonder what these black-box tactics 
   are doing under the hood. For this purpose, there appear to be much fewer resources
   available.

   This is the position I find myself in. In particular, I'm bothered with the ubiquitous 
   tactics which are solving goals that I don't think I could solve manually. So, I plan 
   on digging into these tactics by inspecting their output, and implementing some of my 
   own tactics to mirror their behavior.

   While this series is primarily about *my* quest to understand the important underlying 
   concepts of Coq, I'm writing all of this up in the hopes that someone else might fight 
   them useful. I'm trying to write a guided tour of the darker corners of Coq that I wish 
   I had when I began this indeavor.

   Besides, as the common saying goes: "If you can't explain it simply, you don't understand
   it well enough." Writing this down helps me clarify my own thoughts, and ensure the 
   concepts have sunk in.

   For the purpose of this series, I assume the reader has a level of understanding consistent 
   with having finished the first Software Foundations book. That is, I assume the reader is 
   familiar with the common tactics and commands, as well as a general comfort with functional 
   programming.

   If you're still with me, I appreciate you indulging this clumsy adventure, and I hope 
   I can impart some portion of my revelations on you as well.

   Without further ado, let's jump in to our first topic: equality.
 *)
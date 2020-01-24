/*
SUnitEquations.m

Author: Adela Gherga <adelagherga@gmail.com>
Copyright © 2020, Adela Gherga, all rights reserved.
Created: 23 January 2020

Description: This program generates all S-unit equations corresponding to the Thue-Mahler forms of absolute discriminant <= 10^{10}

Commentary:

To do list:  0. Create the appropriate folders (determine rank possibilities)
      	     1. Write the code
      	     2. Generate appropriate output files
	     3. Port output files onto github or dropbox folder

Example:

*/

/*
Organizational ideas:

1. use bash code to read each line, and use the input to run (this) magma code. This code handles only 1 TM equaiton at a time, and ports the ouput to an apporpriate text file (based on rank, ie number of primes and infinite places);
   Advantages: can parallelize
   Disadvantages: writing bash code is damn hard and I'm not that good at it
   		  won't be able to sort the S-unit equations among each file,
		  will only be able to append them at the end of the files
		  (by rank)


2. Alternatively, this code reads the forms file, and for each on (one at a time), goes through and generates teh S-unit equation and ouptuts it appropriately;

   Advantages: significantly easier to code
	       will be able to further sort the S-unit equations among each
	       file (by more than just rank)
   Disadvantages: parallelization won't be possible here
   		  slow code that might take too long to run


It seems the clear winner is to write bash code that does this. Folder format should be as follows

No. real/complex embeddings (R=0,1,2): 1 folder each
    No of finite places (so total rank should be obvious): 1 folder for each


*/

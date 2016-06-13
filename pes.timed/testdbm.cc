/** \file testdbm.cc
 * The test file for the DBM class. The DBM class is our representation
 * for a clock zone.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @version 1.0
 * @see DBM.hh
 * @date September 20, 2012 */

#include <iostream>
#include "DBM.hh"

using namespace std;


/** Main method for testing the DBM.hh class. Its output
 * is printed to the screen; testers examine its output for errors.
 * @param argc The number of input arguments (the program
 * name is the first argument).
 * @param argv (**) The array of strings containing
 * the program arguments.
 * @return 0: normal exit; -1 or 1: abnormal exit. */
int main(int argc, char** argv){
  
  DBM * tDBM1 = new DBM(3);
	tDBM1->addConstraint(0,0, (0x1));
	tDBM1->addConstraint(0,1, (-1 << 1) + 1);
	tDBM1->addConstraint(0,2,  (-5 << 1) + 1);
	tDBM1->addConstraint(1,0,  (3 << 1) + 1);
	tDBM1->addConstraint(1,1, (0x1));
	tDBM1->addConstraint(1,2, (0xFFF<<1));
	tDBM1->addConstraint(2,0, (7 << 1) + 1);
	tDBM1->addConstraint(2,1,  (0xFFF<<1));
	tDBM1->addConstraint(2,2, (0x1));
	
	DBM * tDBM1p = new DBM(3);
	tDBM1p->addConstraint(0,0, (0x1));
	tDBM1p->addConstraint(0,1, (-1 << 1) + 1);
	tDBM1p->addConstraint(0,2, (-5 << 1) + 1);
	tDBM1p->addConstraint(1,0, (3 << 1) + 1);
	tDBM1p->addConstraint(1,1, (0x1));
	tDBM1p->addConstraint(1,2,  (0xFFF<<1));
	tDBM1p->addConstraint(2,0, (7 << 1) + 1);
	tDBM1p->addConstraint(2,1, (0xFFF<<1));
	tDBM1p->addConstraint(2,2, (0x1));
	
	// Make A test DBM
	DBM * testDBM1 = new DBM(*tDBM1);
	testDBM1->addConstraint(0,0, (0x1));
	testDBM1->addConstraint(0,1, (-1 << 1) + 1);
	testDBM1->addConstraint(0,2, (-5 << 1) + 1);
	testDBM1->addConstraint(1,0, (3 << 1) + 1);
	testDBM1->addConstraint(1,1, (0x1));
	testDBM1->addConstraint(1,2, (0xFFF<<1));
	testDBM1->addConstraint(2,0, (7 << 1) + 1);
	testDBM1->addConstraint(2,1, (0xFFF<<1));
	testDBM1->addConstraint(2,2, (0x1));
	
	DBM * testDBM1b = new DBM(*tDBM1);
	testDBM1b->addConstraint(0,1, (-2 << 1) + 1);
	// Make a second test DBM
	DBM * testDBM2 = new DBM(*tDBM1);
	testDBM2->addConstraint(2,1, (1 << 1) + 1);
	
	// Make a third test DBM
	DBM * testDBM3 = new DBM(3);
	testDBM3->addConstraint(0,0, (0x1));
	testDBM3->addConstraint(0,1, (-3 << 1) + 1);
	testDBM3->addConstraint(0,2, (0xFFF<<1));
	testDBM3->addConstraint(1,0, (0xFFF<<1));
	testDBM3->addConstraint(1,1, (0x1));
	testDBM3->addConstraint(1,2,  (-5 << 1) + 1);
	testDBM3->addConstraint(2,0, (0xFFF<<1));
	testDBM3->addConstraint(2,1, (7 << 1) + 1);
	testDBM3->addConstraint(2,2,  (0x1));
	
	// Make a fourth test DBM - empty
	// This is only empty because the (0, <=) becomes (0,<)
	// and illustrates a bug in cf()
	DBM * testDBM4 = new DBM(3);
	testDBM4->addConstraint(0,0, 0x1);
	testDBM4->addConstraint(0,1, (-3 << 1) + 1);
	testDBM4->addConstraint(0,2, (0xFFF<<1));
	testDBM4->addConstraint(1,0, (3 << 1));
	testDBM4->addConstraint(1,1, (0x1));
	testDBM4->addConstraint(1,2, (0xFFF<<1));
	testDBM4->addConstraint(2,0, (0xFFF<<1));
	testDBM4->addConstraint(2,1, (0xFFF<<1));
	testDBM4->addConstraint(2,2, (0x1));
	
	// Make a fifth test DBM - empty
	DBM * testDBM5 = new DBM(3);
	testDBM5->addConstraint(0,0, (0x1));
	testDBM5->addConstraint(0,1, (-4 << 1) + 1);
	testDBM5->addConstraint(0,2, (0xFFF<<1));
	testDBM5->addConstraint(1,0, (2 << 1));
	testDBM5->addConstraint(1,1, (0x1));
	testDBM5->addConstraint(1,2, (0xFFF<<1));
	testDBM5->addConstraint(2,0, (0xFFF<<1));
	testDBM5->addConstraint(2,1, (0xFFF<<1));
	testDBM5->addConstraint(2,2, (0x1));
	
	// Make a sixth test DBM - empty
	DBM * testDBM6 = new DBM(3);
	testDBM6->addConstraint(0,0, (0x1));
	testDBM6->addConstraint(0,1, (-1 << 1) + 1);
	testDBM6->addConstraint(0,2, (-1 << 1) + 1);
	testDBM6->addConstraint(1,0, (1 << 1) + 1);
	testDBM6->addConstraint(1,1, (0x1));
	testDBM6->addConstraint(1,2, (0 << 1) + 1);
	testDBM6->addConstraint(2,0, (2 << 1));
	testDBM6->addConstraint(2,1, (1 << 1) + 1);
	testDBM6->addConstraint(2,2, (0x1));
	
	// Make a seventh test DBM - empty
	DBM * testDBM7 = new DBM(3);
	testDBM7->addConstraint(0,0, (0x1));
	testDBM7->addConstraint(0,1, (-3 << 1) + 1);
	testDBM7->addConstraint(0,2, (-1 << 1) + 1);
	testDBM7->addConstraint(1,0, (3 << 1) + 1);
	testDBM7->addConstraint(1,1, (0x1));
	testDBM7->addConstraint(1,2, (3 << 1) + 1);
	testDBM7->addConstraint(2,0, (6 << 1));
	testDBM7->addConstraint(2,1, (3 << 1) + 1);
	testDBM7->addConstraint(2,2, (0x1));
	
	DBM *INFTYDBM;
	INFTYDBM = new DBM(3);
  for(int i = 0; i < 3;i++) {
    for(int j = 0; j < 3; j++){
      if(i == j || i == 0){
        INFTYDBM->addConstraint(i,j, 0x1);
      }
      else {
        INFTYDBM->addConstraint(i,j, (0xFFF << 1));
      }
    }
  }
	
	cout << "\nDBM1: IsEmpty: " << testDBM1->emptiness() << "\n";
	testDBM1->print();
	
	testDBM1->cf();
	cout << "\n\nDBM1 in canonical form: IsEmpty: " << testDBM1->emptiness() << "\n";
	testDBM1->print();
	
	tDBM1p->pre();
	cout << "\nDBM1 after pre(): IsEmpty: " << tDBM1p->emptiness() << "\n";
	tDBM1p->print();
	
	tDBM1p->cf();
	cout << "\n\nDBM1 after pre() in canonical form: IsEmpty: " << tDBM1p->emptiness() << "\n";
	tDBM1p->print();
	
	cout << "\n\nDBM1b: IsEmpty: " << testDBM1b->emptiness() << "\n";
	testDBM1b->print();
  
  
  testDBM1b->cf();
	cout << "\n\nDBM1b in canonical form: IsEmpty: " << testDBM1b->emptiness() << "\n";
	testDBM1b->print();
	
	cout << "\n\nDBM2: IsEmpty: " << testDBM2->emptiness() << "\n";
	testDBM2->print();
  
  testDBM2->cf();
	cout << "\n\nDBM2 in canonical form: IsEmpty: " << testDBM2->emptiness() << "\n";
	testDBM2->print();
	
	testDBM2->bound(3);
	cout << "\n\nDBM2 bounded with maxc=3: IsEmpty: " << testDBM2->emptiness() << "\n";
	testDBM2->print();
	
	cout << "\n\nDBM3: IsEmpty: " << testDBM3->emptiness() << "\n";
	testDBM3->print();
  
  testDBM3->cf();
	cout << "\n\nDBM3 in canonical form: IsEmpty: " << testDBM3->emptiness() << "\n";
	testDBM3->print();
	
	
	cout << "\n\nDBM4: IsEmpty: " << testDBM4->emptiness() << "\n";
	testDBM4->print();
  
  testDBM4->cf();
	cout << "\n\nDBM4 in canonical form: IsEmpty: " << testDBM4->emptiness() << "\n";
	testDBM4->print();
	
	cout << "\n\nDBM5: IsEmpty: " << testDBM5->emptiness() << "\n";
	testDBM5->print();
  
  testDBM5->cf();
	cout << "\n\nDBM5 in canonical form: IsEmpty: " << testDBM5->emptiness() << "\n";
	testDBM5->print();
	
	cout << "\n\nDBM6: IsEmpty: " << testDBM6->emptiness() << "\n";
	testDBM6->print();
  
  testDBM6->cf();
	cout << "\n\nDBM6 in canonical form: IsEmpty: " << testDBM6->emptiness() << "\n";
	testDBM6->print();
	
	cout << "\n\nDBM7: IsEmpty: " << testDBM7->emptiness() << "\n";
	testDBM7->print();
  
  testDBM7->cf();
	cout << "\n\nDBM7 in canonical form: IsEmpty: " << testDBM7->emptiness() << "\n";
	testDBM7->print();
	
	DBM testDBM7b(*testDBM7);
	DBM *testDBM8 = new DBM(*testDBM7);
	DBM testDBM7c(*testDBM7);
	DBM *testDBM9 = &testDBM7c;
	
	testDBM7b & *testDBM6;
	
	cout << "\n\nDBM7 ^ DBM6 via testDBM7b IsEmpty: " << testDBM7b.emptiness() << "\n";
	testDBM7b.print();
  
  testDBM7b.cf();
	cout << "\n\nDBM7 ^ DBM6 via testDBM7b in canonical form: IsEmpty: " << testDBM7b.emptiness() << "\n";
	testDBM7b.print();
	
	*testDBM8 & *testDBM6;
	
	cout << "\n\nDBM7 ^ DBM6 via testDBM8 IsEmpty: " << testDBM8->emptiness() << "\n";
	testDBM8->print();
  
  testDBM8->cf();
	cout << "\n\nDBM7 ^ DBM6 via testDBM8 in canonical form: IsEmpty: " << testDBM8->emptiness() << "\n";
	testDBM8->print();
	
	
	cout << "\n\nDBM7 via testDBM7c IsEmpty: " << testDBM7c.emptiness() << "\n";
	testDBM7c.print();
  
  testDBM7c.cf();
	cout << "\n\nDBM7 via testDBM7c in canonical form: IsEmpty: " << testDBM7c.emptiness() << "\n";
	testDBM7c.print();
	
	*testDBM9 & *testDBM6;
	
	cout << "\n\nDBM7 ^ DBM6 via testDBM9 IsEmpty: " << testDBM9->emptiness() << "\n";
	testDBM9->print();
  
  testDBM9->cf();
	cout << "\n\nDBM7 ^ DBM6 via testDBM9 in canonical form: IsEmpty: " << testDBM9->emptiness() << "\n";
	testDBM9->print();
	
	cout << "\n\nDBM7 ^ DBM6 via testDBM7c/9 IsEmpty: " << testDBM7c.emptiness() << "\n";
	testDBM7c.print();
  
  testDBM7c.cf();
	cout << "\n\nDBM7 ^ DBM6 via testDBM7c/9 in canonical form: IsEmpty: " << testDBM7c.emptiness() << "\n";
	testDBM7c.print();
	
	cout << "\n\nINFTYDBM: IsEmpty: " << INFTYDBM->emptiness() << "\n";
	INFTYDBM->print();
  
  INFTYDBM->cf();
	cout << "\n\nINFTYDBM in canonical form: IsEmpty: " << INFTYDBM->emptiness() << "\n";
	INFTYDBM->print();
	
	DBM *ccrepA = new DBM(5);
  for (int i=0; i<5; i++) {
    ccrepA->addConstraint(i,0, 0x1);
  }
  
  cout << "\n\nccrepA: IsEmpty: " << ccrepA->emptiness() << "\n";
	ccrepA->print();
  
  ccrepA->cf();
	cout << "\n\nccrepA in canonical form: IsEmpty: " << ccrepA->emptiness() << "\n";
	ccrepA->print();
	
	DBM * EMPTY = new DBM(3);
  for (int i=1; i<3; i++){
    EMPTY->addConstraint(i,0, 0);
    EMPTY->addConstraint(0,i, 0);
  }
	
	cout << "\n\nEMPTY: IsEmpty: " << EMPTY->emptiness() << "\n";
	EMPTY->print();
  
  EMPTY->cf();
	cout << "\n\nEMPTY in canonical form: IsEmpty: " << EMPTY->emptiness() << "\n";
	EMPTY->print();
	
	cout << "----------------------------\n";
	cout << "Extra DBM Tests:\n";
	cout << "-----------------------------\n";
	
	DBM *tDBM5 = new DBM(3);
	tDBM5->addConstraint(0,2, (-3 << 1) + 1);
	tDBM5->addConstraint(1,0, (2 << 1) + 1);
	tDBM5->addConstraint(2,0, (2 << 1) + 1);
	cout << "\n\ntDBM5: IsEmpty: " << tDBM5->emptiness() << "\n";
	tDBM5->print();
  
  tDBM5->cf();
	cout << "\n\ntDBM5 in canonical form: IsEmpty: " << tDBM5->emptiness() << "\n";
	tDBM5->print();
	
	/* Make DBM to try to test the correctnes of bound(maxc) */
	DBM * testDBMBound1 = new DBM(3);
	testDBMBound1->addConstraint(0,0, 0x1);
	testDBMBound1->addConstraint(0,1, (-3 << 1) + 1);
	testDBMBound1->addConstraint(0,2, (0xFFF<<1));
	testDBMBound1->addConstraint(1,0, (0xFFF<<1));
	testDBMBound1->addConstraint(1,1, (0x1));
	testDBMBound1->addConstraint(1,2, (0xFFF<<1));
	testDBMBound1->addConstraint(2,0, (0xFFF<<1));
	testDBMBound1->addConstraint(2,1, (0xFFF<<1));
	testDBMBound1->addConstraint(2,2, (0x1));
	
	cout << "\n\ntestDBMBound1: IsEmpty: " << testDBMBound1->emptiness() << "\n";
	testDBMBound1->print();
	
	testDBMBound1->cf();
	cout << "\n\ntestDBMBound1 in canonical form: IsEmpty: " << testDBMBound1->emptiness() << "\n";
	testDBMBound1->print();
	
	testDBMBound1->bound(2);
	cout << "\n\ntestDBMBound1 after normalization with maxc = 2: IsEmpty: " << testDBMBound1->emptiness() << "\n";
	testDBMBound1->print();
	
	/* Make DBM to try to test the correctnes of bound(maxc) */
	DBM * testDBMBound2 = new DBM(3);
	testDBMBound2->addConstraint(0,0, 0x1);
	testDBMBound2->addConstraint(0,1, (-5 << 1) + 1);
	testDBMBound2->addConstraint(0,2, (0xFFF<<1));
	testDBMBound2->addConstraint(1,0, (0xFFF<<1));
	testDBMBound2->addConstraint(1,1, (0x1));
	testDBMBound2->addConstraint(1,2, (0xFFF<<1));
	testDBMBound2->addConstraint(2,0, (0xFFF<<1));
	testDBMBound2->addConstraint(2,1, (2<<1) + 1);
	testDBMBound2->addConstraint(2,2, (0x1));
	
	cout << "\n\ntestDBMBound2: IsEmpty: " << testDBMBound2->emptiness() << "\n";
	testDBMBound2->print();
	
	testDBMBound2->cf();
	cout << "\n\ntestDBMBound2 in canonical form: IsEmpty: " << testDBMBound2->emptiness() << "\n";
	testDBMBound2->print();
	
	testDBMBound2->bound(4);
	cout << "\n\ntestDBMBound2 after normalization with maxc = 4: IsEmpty: " << testDBMBound2->emptiness() << "\n";
	testDBMBound2->print();
	
	/* Make DBM to try to test the correctnes of bound(maxc) */
	DBM * testDBMBound3 = new DBM(3);
	testDBMBound3->addConstraint(0,0, 0x1);
	testDBMBound3->addConstraint(0,1, (-5 << 1) + 1);
	testDBMBound3->addConstraint(0,2, (0xFFF<<1));
	testDBMBound3->addConstraint(1,0, (0xFFF<<1));
	testDBMBound3->addConstraint(1,1, (0x1));
	testDBMBound3->addConstraint(1,2, (0xFFF<<1));
	testDBMBound3->addConstraint(2,0, (1<<1)+1);
	testDBMBound3->addConstraint(2,1, (2 <<1)+1);
	testDBMBound3->addConstraint(2,2, (0x1));
	
	cout << "\n\ntestDBMBound3: IsEmpty: " << testDBMBound3->emptiness() << "\n";
	testDBMBound3->print();
	
	testDBMBound3->cf();
	cout << "\n\ntestDBMBound3 in canonical form: IsEmpty: " << testDBMBound3->emptiness() << "\n";
	testDBMBound3->print();
	
	testDBMBound3->bound(4);
	cout << "\n\ntestDBMBound3 after normalization with maxc = 4: IsEmpty: " << testDBMBound3->emptiness() << "\n";
	testDBMBound3->print();
	
	/* Make DBM to try to test the correctnes of bound(maxc) */
	DBM * testDBMBound4 = new DBM(3);
	testDBMBound4->addConstraint(0,0, 0x1);
	testDBMBound4->addConstraint(0,1, (-5 << 1) + 1);
	testDBMBound4->addConstraint(0,2, (0xFFF<<1));
	testDBMBound4->addConstraint(1,0, (0xFFF<<1));
	testDBMBound4->addConstraint(1,1, (0x1));
	testDBMBound4->addConstraint(1,2, (0xFFF<<1));
	testDBMBound4->addConstraint(2,0, (0<<1)+1);
	testDBMBound4->addConstraint(2,1, (2<<1)+1);
	testDBMBound4->addConstraint(2,2, (0x1));
	
	cout << "\n\ntestDBMBound4: IsEmpty: " << testDBMBound4->emptiness() << "\n";
	testDBMBound4->print();
	
	testDBMBound4->cf();
	cout << "\n\ntestDBMBound4 in canonical form: IsEmpty: " << testDBMBound4->emptiness() << "\n";
	testDBMBound4->print();
	
	testDBMBound4->bound(4);
	cout << "\n\ntestDBMBound4 after normalization with maxc = 4: IsEmpty: " << testDBMBound4->emptiness() << "\n";
	testDBMBound4->print();
	
	/* Make DBM to try to test the correctnes of bound(maxc) */
	DBM * testDBMBound5 = new DBM(3);
	testDBMBound5->addConstraint(0,0, 0x1);
	testDBMBound5->addConstraint(0,1, (-5 << 1) + 1);
	testDBMBound5->addConstraint(0,2, (0xFFF<<1));
	testDBMBound5->addConstraint(1,0, (0xFFF<<1));
	testDBMBound5->addConstraint(1,1, (0x1));
	testDBMBound5->addConstraint(1,2, (0xFFF<<1));
	testDBMBound5->addConstraint(2,0, (-1 <<1)+1);
	testDBMBound5->addConstraint(2,1, (2<<1)+1);
	testDBMBound5->addConstraint(2,2, (0x1));
	
	cout << "\n\ntestDBMBound5: IsEmpty: " << testDBMBound5->emptiness() << "\n";
	testDBMBound5->print();
	
	testDBMBound5->cf();
	cout << "\n\ntestDBMBound5 in canonical form: IsEmpty: " << testDBMBound5->emptiness() << "\n";
	testDBMBound5->print();
	
	testDBMBound5->bound(4);
	cout << "\n\ntestDBMBound5 after normalization with maxc = 4: IsEmpty: " << testDBMBound5->emptiness() << "\n";
	testDBMBound5->print();
	
	/* Make DBM to try to test the correctnes of bound(maxc) */
	DBM * testDBMBound6 = new DBM(3);
	testDBMBound6->addConstraint(0,0, 0x1);
	testDBMBound6->addConstraint(0,1, (-2 << 1) + 1);
	testDBMBound6->addConstraint(0,2, (0xFFF<<1));
	testDBMBound6->addConstraint(1,0, (0xFFF<<1));
	testDBMBound6->addConstraint(1,1, (0x1));
	testDBMBound6->addConstraint(1,2, (1<<1));
	testDBMBound6->addConstraint(2,0, (0xFFF<<1));
	testDBMBound6->addConstraint(2,1, (0xFFF<<1));
	testDBMBound6->addConstraint(2,2, (0x1));
	
	cout << "\n\ntestDBMBound6: IsEmpty: " << testDBMBound6->emptiness() << "\n";
	testDBMBound6->print();
	
	testDBMBound6->cf();
	cout << "\n\ntestDBMBound6 in canonical form: IsEmpty: " << testDBMBound6->emptiness() << "\n";
	testDBMBound6->print();
	
	testDBMBound6->bound(1);
	cout << "\n\ntestDBMBound6 after normalization with maxc = 1: IsEmpty: " << testDBMBound6->emptiness() << "\n";
	testDBMBound6->print();
	
	testDBMBound6->cf();
	cout << "\n\ntestDBMBound6 in canonical form after maxc = 1 normalization: IsEmpty: " << testDBMBound6->emptiness() << "\n";
	testDBMBound6->print();
	
	/* Make DBM to try to test the correctnes of emptiness()
	 * try to see why we cannot just check the diagonals */
	DBM * testDBMEmpty1 = new DBM(3);
	testDBMEmpty1->addConstraint(0,0, 0x1);
	testDBMEmpty1->addConstraint(0,1, (-5 << 1) + 1);
	testDBMEmpty1->addConstraint(0,2, (0xFFF<<1));
	testDBMEmpty1->addConstraint(1,0, (0xFFF<<1));
	testDBMEmpty1->addConstraint(1,1, (0x1));
	testDBMEmpty1->addConstraint(1,2, (0xFFF<<1));
	testDBMEmpty1->addConstraint(2,0, (0xFFF<<1));
	testDBMEmpty1->addConstraint(2,1, (2 << 1) + 1);
	testDBMEmpty1->addConstraint(2,2, (0x1));
	
	cout << "\n\ntestDBMEmpty1: IsEmpty: " << testDBMEmpty1->emptiness() << "\n";
	testDBMEmpty1->print();
	
	testDBMEmpty1->cf();
	cout << "\n\ntestDBMEmpty1 in canonical form: IsEmpty: " << testDBMEmpty1->emptiness() << "\n";
	testDBMEmpty1->print();
	
	testDBMEmpty1->bound(4);
	cout << "\n\ntestDBMEmpty1 after normalization with maxc = 4: IsEmpty: " << testDBMEmpty1->emptiness() << "\n";
	testDBMEmpty1->print();
	
	testDBMEmpty1->cf();
	cout << "\n\ntestDBMEmpty1 in canonical form after maxc = 4 normalization: IsEmpty: " << testDBMEmpty1->emptiness() << "\n";
	testDBMEmpty1->print();
	
	
	DBM * myDBM1 = new DBM(4);
	myDBM1->addConstraint(0,1, (-1 << 1) + 1);
	myDBM1->addConstraint(3,1, (6 << 1) + 1);
	myDBM1->addConstraint(3,2, (4 << 1) + 1);
	
	DBM * myDBM1a1 = new DBM(4);
	myDBM1a1->addConstraint(0,1, (-1 << 1) + 1);
	myDBM1a1->addConstraint(3,2, (4 << 1) + 1);
	
	DBM * myDBM1a2 = new DBM(4);
	myDBM1a2->addConstraint(3,1, (6 << 1) + 1);
	myDBM1a2->addConstraint(3,2, (4 << 1) + 1);
	
	DBM * myDBM2 = new DBM(4);
	myDBM2->addConstraint(2,0,(3 << 1) + 1);
	
	DBM * myDBM2b = new DBM(*myDBM2);
	
	cout << "\n\nmyDBM1: IsEmpty: " << myDBM1->emptiness() << "\n";
	myDBM1->print();
	
	myDBM1->cf();
	cout << "\n\nmyDBM1 in canonical form: IsEmpty: " << myDBM1->emptiness() << "\n";
	myDBM1->print();
	
	cout << "\n\nmyDBM1a1: IsEmpty: " << myDBM1a1->emptiness() << "\n";
	myDBM1a1->print();
	
	myDBM1a1->cf();
	cout << "\n\nmyDBM1a1 in canonical form: IsEmpty: " << myDBM1a1->emptiness() << "\n";
	myDBM1a1->print();
	
	cout << "\n\nmyDBM1a2: IsEmpty: " << myDBM1a2->emptiness() << "\n";
	myDBM1a2->print();
	
	myDBM1->cf();
	cout << "\n\nmyDBM1a2 in canonical form: IsEmpty: " << myDBM1a2->emptiness() << "\n";
	myDBM1a2->print();
	
	cout << "\n\nmyDBM2: IsEmpty: " << myDBM2->emptiness() << "\n";
	myDBM2->print();
	
	myDBM2->cf();
	cout << "\n\nmyDBM2 in canonical form: IsEmpty: " << myDBM2->emptiness() << "\n";
	myDBM2->print();
	
	*myDBM2 & *myDBM1;
	
	cout << "\n\nmyDBM2 & myDBM1: IsEmpty: " << myDBM2->emptiness() << "\n";
	myDBM2->print();
	
	myDBM2->cf();
	cout << "\n\nmyDBM2 & myDBM1 in canonical form: IsEmpty: " << myDBM2->emptiness() << "\n";
	myDBM2->print();
	
	delete myDBM2;
	myDBM2 = new DBM(*myDBM2b);
	
	*myDBM2 & *myDBM1a1;
	
	cout << "\n\nmyDBM2 & myDBM1a1: IsEmpty: " << myDBM2->emptiness() << "\n";
	myDBM2->print();
	
	myDBM2->cf();
	cout << "\n\nmyDBM2 & myDBM1a1 in canonical form: IsEmpty: " << myDBM2->emptiness() << "\n";
	myDBM2->print();
	
	delete myDBM2;
	myDBM2 = new DBM(*myDBM2b);
	
	*myDBM2 & *myDBM1a2;
	
	cout << "\n\nmyDBM2 & myDBM1a2: IsEmpty: " << myDBM2->emptiness() << "\n";
	myDBM2->print();
	
	myDBM2->cf();
	cout << "\n\nmyDBM2 & myDBM1a2 in canonical form: IsEmpty: " << myDBM2->emptiness() << "\n";
	myDBM2->print();
	
	
	cout << endl;
	
	DBM * d3 = NULL;
	delete d3;
	
	// Now delete all DBMS to eliminate memory leaks:
	delete tDBM1;
	delete tDBM1p;
	delete testDBM1;
	delete testDBM1b;
	delete testDBM2;
	delete testDBM3;
	delete testDBM4;
	delete testDBM5;
	delete testDBM6;
	delete testDBM7;
	delete testDBM8;
	delete INFTYDBM;
	delete ccrepA;
	delete EMPTY;
	delete tDBM5;
	delete testDBMBound1;
	delete testDBMBound2;
	delete testDBMBound3;
	delete testDBMBound4;
	delete testDBMBound5;
	delete testDBMBound6;
	delete testDBMEmpty1;
	delete myDBM1;
	delete myDBM1a1;
	delete myDBM1a2;
	delete myDBM2;
	delete myDBM2b;
	
	return 0;
}


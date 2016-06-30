/** \file testdbmlist.cc
 * The test file for the DBM List class. The DBMList class is our representation
 * for a union of DBMs (DBMs are clock zones).
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @version 1.0
 * @see DBM.hh, DBMList.hh
 * @date September 20, 2012 */

#include <iostream>
#include "DBM.hh"
#include "DBMList.hh"

using namespace std;

/** Main method for testing the DBMList.hh class. Its output
 * is printed to the screen; testers examine its output for errors.
 * @param argc The number of input arguments (the program
 * name is the first argument).
 * @param argv (**) The array of strings containing
 * the program arguments.
 * @return 0: normal exit; -1 or 1: abnormal exit.  */
int main(int argc, char** argv){
  
  DBM * tDBM1t = new DBM(3);
	tDBM1t->addConstraint(0,0, (0x1));
	tDBM1t->addConstraint(0,1, (-1 << 1) + 1);
	tDBM1t->addConstraint(0,2,  (-5 << 1) + 1);
	tDBM1t->addConstraint(1,0,  (3 << 1) + 1);
	tDBM1t->addConstraint(1,1, (0x1));
	tDBM1t->addConstraint(1,2, (0xFFF<<1));
	tDBM1t->addConstraint(2,0, (7 << 1) + 1);
	tDBM1t->addConstraint(2,1,  (0xFFF<<1));
	tDBM1t->addConstraint(2,2, (0x1));
	DBMList * tDBM1 = new DBMList(*tDBM1t);
	
	DBM * tDBM1pt = new DBM(3);
	tDBM1pt->addConstraint(0,0, (0x1));
	tDBM1pt->addConstraint(0,1, (-1 << 1) + 1);
	tDBM1pt->addConstraint(0,2, (-5 << 1) + 1);
	tDBM1pt->addConstraint(1,0, (3 << 1) + 1);
	tDBM1pt->addConstraint(1,1, (0x1));
	tDBM1pt->addConstraint(1,2,  (0xFFF<<1));
	tDBM1pt->addConstraint(2,0, (7 << 1) + 1);
	tDBM1pt->addConstraint(2,1, (0xFFF<<1));
	tDBM1pt->addConstraint(2,2, (0x1));
  DBMList * tDBM1p = new DBMList(*tDBM1pt);
  
  DBMList * list1 = new DBMList(3);
  
  
  DBM * l1b = new DBM(3, 0,1, (-1 << 1) + 1);
  DBMList * list1b = new DBMList(*l1b);
  
  list1->addDBM(*l1b);
  
  DBM * l3a = new DBM(3);
  l3a->addConstraint(1,0, (3 << 1) + 1);
  l3a->addConstraint(2,0, (3 << 1) + 1);
  DBM * l3b = new DBM(3);
  l3b->addConstraint(1,0, (4 << 1));
  l3b->addConstraint(2,0, (4 << 1));
  l3b->addConstraint(0,1, (-2 << 1) + 1);
  l3b->addConstraint(0,2, (-2 << 1) + 1);
  DBM * l3c = new DBM(3);
  l3c->addConstraint(2,1, (0 << 1) );
  DBMList * list3 = new DBMList(*l3a);
  list3->addDBM(*l3b);
  list3->addDBM(*l3c);
  
  DBM * l4a = new DBM(3);
  l4a->addConstraint(1,0, (1 << 1));
  l4a->addConstraint(0,1, (-2 << 1) + 1);
  DBMList *list4 = new DBMList(*l4a);
  
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
  
  DBM * EMPTY = new DBM(3);
  for (int i=1; i<3; i++){
    EMPTY->addConstraint(i,0, 0);
    EMPTY->addConstraint(0,i, 0);
  }
	
	/* Here is the x < 1 || x >= 1 DBM for starter tests */
	DBM * d2a = new DBM(3);
	d2a->addConstraint(0,1, (-1 << 1) + 1);
	d2a->cf();
	DBM * d2b = new DBM(3);
	d2b->addConstraint(1,0, (1 << 1));
	d2b->cf();
	DBMList * dList2 = new DBMList(*d2a);
	dList2->addDBM(*d2b);
	
	DBMList *dList2copy = new DBMList(*dList2);
	
	
	cout << "\n\nDBMList 1: IsEmpty: " << tDBM1->emptiness() << "\n";
	tDBM1->print(cout);
	tDBM1->cf();
	cout << "\n\nDBMList 1 in canonical form: IsEmpty: " << tDBM1->emptiness() << "\n";
	tDBM1->print(cout);
	
	tDBM1p->pre();
	cout << "\nDBMList 1 after pre(): IsEmpty: " << tDBM1p->emptiness() << "\n";
	tDBM1p->print(cout);
	
	tDBM1p->cf();
	cout << "\n\nDBMList 1 after pre() in canonical form: IsEmpty: " << tDBM1p->emptiness() << "\n";
	tDBM1p->print(cout);
  
	cout << "\n\nlist 1: IsEmpty: " << list1->emptiness() << "\n";
	list1->print(cout);
	list1->cf();
	cout << "\n\nlist 1 in canonical form: IsEmpty: " << list1->emptiness() << "\n";
	list1->print(cout);
	
	cout << "\n\nlist 1b: IsEmpty: " << list1b->emptiness() << "\n";
	list1b->print(cout);
	list1b->cf();
	cout << "\n\nlist1b in canonical form: IsEmpty: " << list1b->emptiness() << "\n";
	list1b->print(cout);
	
	bool tempBool = (*list1) <= (*INFTYDBM);
	cout << "\n(*list1) <= (*INFTYDBM) " << tempBool << endl;
	tempBool = (*list1 >= *INFTYDBM);
	cout << "(*list1) >= (*INFTYDBM) " << tempBool << endl;
	tempBool = (*list1 == *INFTYDBM);
	cout << "(*list1) == (*INFTYDBM) " << tempBool << endl;
	
	tempBool = (*list1b <= *INFTYDBM);
	cout << "\n(*list1b) <= (*INFTYDBM) " << tempBool << endl;
	tempBool = (*list1b >= *INFTYDBM);
	cout << "(*list1b) >= (*INFTYDBM) " << tempBool << endl;
	tempBool = (*list1b == *INFTYDBM);
	cout << "(*list1b) == (*INFTYDBM) " << tempBool << endl;
	
	tempBool = (*list1b <= *list1);
	cout << "\n(*list1b) <= (*list1) " << tempBool << endl;
	tempBool = (*list1b >= *list1);
	cout << "(*list1b) >= (*list1) " << tempBool << endl;
	tempBool = (*list1b == *list1);
	cout << "(*list1b) == (*list1) " << tempBool << endl;
	
	
  tempBool = (*list1 <= *list1b);
	cout << "\n(*list1) <= (*list1b) " << tempBool << endl;
	tempBool = (*list1 >= *list1b);
	cout << "(*list1) >= (*list1b) " << tempBool << endl;
	tempBool = (*list1 == *list1b);
	cout << "(*list1) == (*list1b) " << tempBool << endl;
	
  cout << "\n\ndList2: IsEmpty: " << dList2->emptiness() << "\n";
	dList2->print(cout);
	dList2->cf();
	cout << "\n\ndList2 in canonical form: IsEmpty: " << dList2->emptiness() << "\n";
	dList2->print(cout);
	
	cout << "\n\ndList2copy: IsEmpty: " << dList2copy->emptiness() << "\n";
	dList2copy->print(cout);
	dList2copy->cf();
	cout << "\n\ndList2copy in canonical form: IsEmpty: " << dList2copy->emptiness() << "\n";
	dList2copy->print(cout);
	
	cout << "\n\nINFTYDBM: IsEmpty: " << INFTYDBM->emptiness() << "\n";
	INFTYDBM->print(cout);
	INFTYDBM->cf();
	cout << "\n\nINFTYDBM in canonical form: IsEmpty: " << INFTYDBM->emptiness() << "\n";
	INFTYDBM->print(cout);
	
	tempBool = (*dList2) <= (*INFTYDBM);
	cout << "\n(*dList2) <= (*INFTYDBM) " << tempBool << endl;
	tempBool = (*dList2 >= *INFTYDBM);
	cout << "(*dList2) >= (*INFTYDBM) " << tempBool << endl;
	tempBool = (*dList2 == *INFTYDBM);
	cout << "(*dList2) == (*INFTYDBM) " << tempBool << endl;
	
	/* Check since <=, >=, == should not change the original
	 * DBM */
	cout << "\n\ndList2: IsEmpty: " << dList2->emptiness() << "\n";
	dList2->print(cout);
	
	tempBool = (*dList2) <= (*d2a);
	cout << "\n(*dList2) <= (*d2a) " << tempBool << endl;
	tempBool = (*dList2 >= *d2a);
	cout << "(*dList2) >= (*d2a) " << tempBool << endl;
	tempBool = (*dList2 == *d2a);
	cout << "(*dList2) == (*d2a) " << tempBool << endl;
	
	tempBool = (*dList2) <= (*dList2);
	cout << "\n(*dList2) <= (*dList2) " << tempBool << endl;
	tempBool = (*dList2 >= *dList2);
	cout << "(*dList2) >= (*dList2) " << tempBool << endl;
	tempBool = (*dList2 == *dList2);
	cout << "(*dList2) == (*dList2) " << tempBool << endl;

 	/* Do an intersection test */
	DBMList * dList2copy2 = new DBMList(*dList2);
	
	cout << "\n\ndList2copy2: IsEmpty: " << dList2copy2->emptiness() << "\n";
	dList2copy2->print(cout);
	dList2copy2->cf();
	cout << "\n\ndList2copy2 in canonical form: IsEmpty: " << dList2copy2->emptiness() << "\n";
	dList2copy2->print(cout);
	
	*dList2copy2 & *dList2;
	cout << "\n\ndList2copy2 after self intersection: IsEmpty: " << dList2copy2->emptiness() << "\n";
	dList2copy2->print(cout);
	dList2copy2->cf();
	cout << "\n\ndList2copy2 after self intersection in canonical form: IsEmpty: " << dList2copy2->emptiness() << "\n";
	dList2copy2->print(cout);
	
	cout << "\n\nlist3: IsEmpty: " << list3->emptiness() << "\n";
	list3->print(cout);
	list3->cf();
	cout << "\n\ndlist3 in canonical form: IsEmpty: " << list3->emptiness() << "\n";
	list3->print(cout);
	
	cout << "\n\nlist4: IsEmpty: " << list4->emptiness() << "\n";
	list4->print(cout);
	list4->cf();
	cout << "\n\nlist4 in canonical form: IsEmpty: " << list4->emptiness() << "\n";
	list4->print(cout);
	
	DBMList * list3copy = new DBMList(3);
	// Add this to test method.
	*list3copy = *list3;
	
	tempBool = (*list3) <= (*list3copy);
	cout << "\n(*list3) <= (*list3copy) " << tempBool << endl;
	tempBool = (*list3 >= *list3copy);
	cout << "(*list3) >= (*list3copy) " << tempBool << endl;
	tempBool = (*list3 == *list3copy);
	cout << "(*list3) == (*list3copy) " << tempBool << endl;
	
	(*list3) & (*list3copy);
	cout << "\n\nlist3 after intersection with copy: IsEmpty: " << list3->emptiness() << "\n";
	list3->print(cout);
	list3->cf();
	cout << "\n\nlist3 after intersection with copy: " << list3->emptiness() << "\n";
	list3->print(cout);
	
	tempBool = (*list3) <= (*list3copy);
	cout << "\n(*list3) <= (*list3copy) " << tempBool << endl;
	tempBool = (*list3 >= *list3copy);
	cout << "(*list3) >= (*list3copy) " << tempBool << endl;
	tempBool = (*list3 == *list3copy);
	cout << "(*list3) == (*list3copy) " << tempBool << endl;
	
	tempBool = (*list4) <= (*list3copy);
	cout << "\n(*list4) <= (*list3copy) " << tempBool << endl;
	tempBool = (*list4 >= *list3copy);
	cout << "(*list4) >= (*list3copy) " << tempBool << endl;
	tempBool = (*list4 == *list3copy);
	cout << "(*list4) == (*list3copy) " << tempBool << endl;
	
	
	cout << endl;
	
	
	// Add tests to test the copy constructors of the DBMList
	*list4 = *list3copy;
	cout << "\nAfter *list4 = *list3copy" << endl;
	tempBool = (*list4) <= (*list3copy);
	cout << "\n(*list4) <= (*list3copy) " << tempBool << endl;
	tempBool = (*list4 >= *list3copy);
	cout << "(*list4) >= (*list3copy) " << tempBool << endl;
	tempBool = (*list4 == *list3copy);
	cout << "(*list4) == (*list3copy) " << tempBool << endl;
	cout << "\n\nlist4: IsEmpty: " << list4->emptiness() << "\n";
	list4->print(cout);
	list4->cf();
	cout << "\n\nlist4 in canonical form: IsEmpty: " << list4->emptiness() << "\n";
	list4->print(cout);
	cout << endl;
	
	list4->makeEmpty();
	cout << "\n After list4 is made empty" << endl;
	list4->print(cout);
	list4->cf();
	cout << "\n\nlist4 in canonical form: IsEmpty: " << list4->emptiness() << "\n";
	list4->print(cout);
	cout << endl;
	
	
	
	// Now delete all DBMS to eliminate memory leaks:
	delete tDBM1;
	delete tDBM1t;
	delete tDBM1p;
	delete tDBM1pt;
 	delete list1;
 	delete list1b;
 	delete l1b;
 	delete d2a;
 	delete d2b;
 	delete dList2;
 	delete dList2copy; 	
 	delete dList2copy2;
  delete INFTYDBM;
  delete EMPTY;
	delete l3a;
	delete l3b;
	delete l3c;
	delete list3;
 	delete l4a;
 	delete list3copy;
 	
 	// Check that list4 is still here
 	cout << "\n\nlist4 in canonical form after list3copy deletion: IsEmpty: " << list4->emptiness() << "\n";
	list4->print(cout);
	cout << endl;
	
 	delete list4;
 
 	
	
	return 0;
}


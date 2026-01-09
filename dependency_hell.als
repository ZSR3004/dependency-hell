open util/ordering[State]
open util/boolean

// This holds a "Concrete Package", which is a specfic instance of a
// package. Namely, this one has a version (ie. Git v1). 
//
// ver: The particular version of this concrete package.
// locked: True if we do not let the package manager upgrade this version.
// dependencies: The set of versions that must be installed for this package
//               to work.
// conflicts: The set of versions that cannot be installed at the same time as
//               this package.
sig Version {
    ver:          Int,
    locked:       Bool,

    dependencies: set Version,
    conflicts: set Version 
}

// This is the general package type. For instance, this might represent
// Git, but not a particular git version. This representation allows us
// to group all versions of Git together.
//
// versions: The set of all versions of this package. For example, package A
// 		might have versions 1, 2, and 3.
sig Package {
	versions: set Version
}

// Universe: The set of uninstalled packages that either are needed or generate a conflict
//    when upgrading the target package.
one sig Universe {
	packages: set Package,
	versions: set Version
}

// This is the user's system state. For instance, prior to upgrading, we have 
// exactly what the user previously installed. When the process of upgrading 
// is over (State.last), We will have a new satate with upgraded packages.
//
// installed: The set of versions that are already installed on the system.
sig State {
    installed:  set Version,
	target: 	Package
}

//  ==================
//  Version Contraints
//  ==================

fact symmetricConflicts {
	all v: Version {
	    all c: v.conflicts {
	        v in c.conflicts
	    }
	}
}

fact disjointDependenciesandConflicts {
	all v: Version {
		all d: Version {
			d in v.dependencies
			implies
			d not in v.conflicts
		}

	all c: Version {
			c in v.conflicts
			implies
			c not in v.dependencies
		}
	}
}

fact nonrecursiveDependenciesandConflicts {
	all v: Version | v not in v.dependencies and v not in v.conflicts
}

fact positiveVersion {
    all v: Version | v.ver >= 0
}

//  ==================
//  Package Contraints
//  ==================

fact versionOnlyExistsInExactlyOnePackage {
    all v: Version |
        one p: Package | v in p.versions
}

//  ================
//  State Contraints
//  ================

pred allDependenciesInstalled[s: State] {
    all v: s.installed {
        all d: v.dependencies | d in s.installed
    }
}

pred uniquePackagesInstalled[s: State] {
    all p: Package |
        lone (s.installed & p.versions)
}

pred noConflictingPackagesInstalled[s: State] {
    all v: s.installed | no (v.conflicts & s.installed)
}

pred validUpgradeState[s: State] {
   allDependenciesInstalled[s]
   uniquePackagesInstalled[s]
   noConflictingPackagesInstalled[s]
}

//  ===========================
//  State Transition Contraints
//  ===========================

fact keepConsistentTarget {
	all s: State - first | first.target = s.target 
}

pred installPackage[s1, s2: State] {
	some p: Package {
		some v: p.versions {
			v not in s1.installed
			s2.installed = s1.installed + v
		}
	}
}

pred upgradePackage[s1, s2: State] {
	some p: Package {
		some disj v1, v2: p.versions {
			v1 in s1.installed
			v1.ver < v2.ver
			s2.installed = s1.installed - v1 + v2
		}
	}
}

pred deletePackage[s1, s2: State] {
    some v: s1.installed {
        v not in s1.installed.dependencies
        s2.installed = s1.installed - v
    }
}

pred respectLock[s1, s2: State] {
    all v: s1.installed {
        v.locked = True
		implies
        v in s2.installed
    }
}

pred validOperation[s1, s2: State] {
    installPackage[s1, s2] 
	or
	upgradePackage[s1, s2]
	or 
	deletePackage[s1, s2]
}

pred oneOperation[s1, s2: State] {
	let diff = (s1.installed - s2.installed) + (s2.installed - s1.installed) {
		#diff = 1
	}
}

pred validTransition[s1, s2: State] {
  	validOperation[s1, s2]
	oneOperation[s1, s2]
	respectLock[s1, s2]
}

//  ============
//  Upgrade Plan
//  ============

pred packageUpgraded[s: State] {
    some f: first.installed & s.target.versions,
        l: s.installed & s.target.versions {
        f.ver < l.ver
    }
}

pred upgradePlan {
	validUpgradeState[first] // For some reason it would sometime not check this.
	all s: State | validUpgradeState[s]
	all s: State - last | validTransition[s, s.next]
	some s: State | packageUpgraded[s]
}

//  ============================
//  Examples and Counterexamples
//  ============================

pred setupVersion[	v: Version, 
					vnum: Int, 
					isLocked: Bool, 
					deps: set Version, 
					confs: set Version] {
	v.ver = vnum
	v.locked = isLocked
	v.dependencies = deps
	v.conflicts = confs
}

// A very simple example where 
pred simpleExample {
	some disj A, B, C: Package {
		Universe.packages = A + B + C
		Package in Universe.packages
		some disj Av1, Av2, Bv1, Cv1, Cv2: Version {
			Universe.versions = Av1 + Av2 + Bv1 + Cv1 + Cv2
			Version in Universe.versions
			
			setupVersion[Av1, 1, False, Bv1 + Cv1, none]
			setupVersion[Av2, 2, False, Bv1 + Cv2, Cv1]
			setupVersion[Bv1, 1, False, none, none]
			setupVersion[Cv1, 1, False, none, Av2]
			setupVersion[Cv2, 2, False, none, none]

			A.versions = Av1 + Av2
			B.versions = Bv1
			C.versions = Cv1 + Cv2		
			
			first.target = A
			first.installed = Av1 + Bv1 + Cv1
		}
	}
}


pred simpleExample2 {
	some disj A, B, C, D: Package {
		Universe.packages = A + B + C + D
		Package in Universe.packages
		some disj Av1, Av2, Bv1, Cv1, Cv2, Dv1, Dv2: Version {
			Universe.versions = Av1 + Av2 + Bv1 + Cv1 + Cv2 + Dv1 + Dv2
			Version in Universe.versions
			
			setupVersion[Av1, 1, False, Bv1 + Cv1, none]
			setupVersion[Av2, 2, False, Bv1 + Cv2, Cv1]
			setupVersion[Bv1, 1, False, none, none]
			setupVersion[Cv1, 1, False, none, Av2]
			setupVersion[Cv2, 2, False, none, none]
			setupVersion[Dv1, 1, True, none, none]
			setupVersion[Dv2, 2, True, none, none]

			A.versions = Av1 + Av2
			B.versions = Bv1
			C.versions = Cv1 + Cv2	
			D.versions = Dv1 + Dv2
			
			first.target = A
			first.installed = Av1 + Bv1 + Cv1 + Dv1
		}
	}
}

pred DualDependenciesExample {
	some disj A, B, C, D: Package {
		Universe.packages = A + B + C + D
		Package in Universe.packages
		some disj Av1, Av2, Bv1, Cv1, Dv1, Dv2: Version {
			Universe.versions = Av1 + Av2 + Bv1 + Cv1 + Dv1 + Dv2
			Version in Universe.versions
			
			setupVersion[Av1, 1, False, Bv1 + Cv1, none]
			setupVersion[Av2, 2, False, Bv1 + Cv1, Dv1]	
			setupVersion[Bv1, 1, False, Dv1, none]
			setupVersion[Cv1, 1, False, none, none]
			setupVersion[Dv1, 1, False, none, Av2]
			setupVersion[Dv2, 2, False, none, none]

			A.versions = Av1 + Av2
			B.versions = Bv1
			C.versions = Cv1
			D.versions = Dv1 + Dv2

			first.target = A
			first.installed = Av1 + Bv1 + Cv1 + Dv1
		}
	}
}

pred DualDependenciesNonexample {
	some disj A, B, C, D: Package {
		Universe.packages = A + B + C + D
		Package in Universe.packages
		some disj Av1, Av2, Bv1, Cv1, Dv1, Dv2: Version {
			Universe.versions = Av1 + Av2 + Bv1 + Cv1 + Dv1 + Dv2
			Version in Universe.versions
			
			setupVersion[Av1, 1, False, Bv1 + Cv1, none]
			setupVersion[Av2, 2, False, Bv1 + Cv1 + Dv2, none]	
			setupVersion[Bv1, 1, False, Dv1, none]
			setupVersion[Cv1, 1, False, none, none]
			setupVersion[Dv1, 1, False, none, none]
			setupVersion[Dv2, 2, False, none, none]

			A.versions = Av1 + Av2
			B.versions = Bv1
			C.versions = Cv1
			D.versions = Dv1 + Dv2

			first.target = A
			first.installed = Av1 + Bv1 + Cv1 + Dv1
		}
	}
}

pred DualDependenciesLockedNonexample {
	some disj A, B, C, D: Package {
		Universe.packages = A + B + C + D
		Package in Universe.packages
		some disj Av1, Av2, Bv1, Cv1, Dv1, Dv2: Version {
			Universe.versions = Av1 + Av2 + Bv1 + Cv1 + Dv1 + Dv2
			Version in Universe.versions
			
			setupVersion[Av1, 1, False, Bv1 + Cv1, none]
			setupVersion[Av2, 2, False, Bv1 + Cv1, Dv1]	
			setupVersion[Bv1, 1, False, Dv1, none]
			setupVersion[Cv1, 1, False, none, none]
			setupVersion[Dv1, 1, True, none, Av2]
			setupVersion[Dv2, 2, False, none, none]

			A.versions = Av1 + Av2
			B.versions = Bv1
			C.versions = Cv1
			D.versions = Dv1 + Dv2

			first.target = A
			first.installed = Av1 + Bv1 + Cv1 + Dv1
		}
	}
}

// ====================
// Running the Examples
// ====================

// simpleExample
run simpleExample for exactly 5 Version, exactly 3 Package, 1 State

pred upgradeSimpleExample {
	simpleExample
	upgradePlan
}

run upgradeSimpleExample for exactly 5 Version, exactly 3 Package, 5 State

// simpleExample2
run simpleExample2 for exactly 7 Version, exactly 4 Package, 1 State

pred upgradeSimpleExample2 {
	simpleExample2
	upgradePlan
}

run upgradeSimpleExample2 for exactly 7 Version, exactly 4 Package, 5 State

//DualDependenciesExample
run DualDependenciesExample for exactly 6 Version, exactly 4 Package, 1 State

pred upgradeDualDependenciesExample {
	DualDependenciesExample
	upgradePlan
}

// DualDependenciesNonexample 
run DualDependenciesNonexample for exactly 6 Version, exactly 4 Package, 1 State

assert DualDependenciesInvalid {
	DualDependenciesNonexample
	implies
	not upgradePlan
}

check DualDependenciesInvalid for exactly 6 Version, exactly 4 Package, 10 State

// DualDependenciesLockedNonexample 
run DualDependenciesLockedNonexample for exactly 6 Version, exactly 4 Package, 1 State

assert DualDependenciesLockedNonexampleInvalid {
	DualDependenciesLockedNonexample
	implies
	not upgradePlan
}

check DualDependenciesLockedNonexampleInvalid for exactly 6 Version, exactly 4 Package, 10 State

//  ==========
//  Assertions
//  ==========
assert noConflictsBetweenDependencies {
	upgradePlan 
	implies
    all s: State {
		all v1: s.installed, v2: v1.dependencies | no (v2.conflicts & s.installed)
	}
}

assert allUniquePackages {
    upgradePlan 
	implies
 	all s: State {
		all p: Package | lone (s.installed & p.versions)
	}
}

assert allDependenciesInstalled {
	upgradePlan
	implies
	all s: State {
		all v: s.installed | v.dependencies in s.installed
	}
}

assert lockRespected {
	upgradePlan
	implies
	all s1, s2: State {
		s2 in s1.*next
		implies
		all v: s1.installed | v.locked = True implies v in s2.installed
	}
}

assert validOperation {
	upgradePlan 
	implies
	all s1, s2: State { 
		s2 in s1.next 	
		implies 
		(
			installPackage[s1, s2] or 
			upgradePackage[s1, s2] or 
			deletePackage[s1, s2]
        )
	}
}

assert oneOperation {
	upgradePlan
	implies
	all s1, s2: State {
		s2 in s1.next
		implies
        #((s1.installed - s2.installed) + (s2.installed - s1.installed)) = 1
	}
}

assert targetUpgraded {
	upgradePlan 
	implies
	some s: State | packageUpgraded[s]
}

assert dependenciesAlwaysPresent {
    upgradePlan implies
        all s: State {
            all v: s.installed | v.dependencies in s.installed
        }
}

assert noEmptyOperations {
	upgradePlan
	implies
	all s1, s2: State {
		s2 in s1.next
		implies
		some (s1.installed - s2.installed) + (s2.installed - s1.installed)
	}
}

assert noTransitiveConflicts {
	upgradePlan
	implies
	all s: State {
		all v: s.installed | no (v.dependencies.*dependencies & v.conflicts)
	}
}

assert transitiveDependencies {
	upgradePlan 
	implies
	all s: State | all v: s.installed | v.dependencies in s.installed
}

check noConflictsBetweenDependencies for exactly 6 Version, exactly 4 Package, 10 State
check allUniquePackages for exactly 6 Version, exactly 4 Package, 10 State
check allDependenciesInstalled for exactly 6 Version, exactly 4 Package, 10 State
check lockRespected for exactly 6 Version, exactly 4 Package, 10 State
check validOperation for exactly 6 Version, exactly 4 Package, 10 State
check oneOperation for exactly 6 Version, exactly 4 Package, 10 State
check targetUpgraded for exactly 6 Version, exactly 4 Package, 10 State
check dependenciesAlwaysPresent for exactly 6 Version, exactly 4 Package, 10 State
check noEmptyOperations for exactly 6 Version, exactly 4 Package, 10 State
check noTransitiveConflicts for exactly 6 Version, exactly 4 Package, 10 State
check transitiveDependencies for exactly 6 Version, exactly 4 Package, 10 State

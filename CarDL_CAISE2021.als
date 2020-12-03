module carDL_CAISE2021

// General Signatures
abstract sig TOP { 
	categorizes: set Type,
	isDerivedFrom: set EndurantType,
	isProperPartOf: set TOP,
	partitions: set TOP,
	standsIn: set Situation}
sig BOTTOM in TOP {} fact { #BOTTOM = 0 } 

// Specific Signatures
sig AbstractIndividual in TOP  {} 
sig AbstractIndividualType in TOP  {} 
sig AntiRigidType in TOP  {} 
sig Aspect in TOP  { 
	inheresIn: set ConcreteIndividual,
	isAspectProperPartOf: set Aspect,
	manifestedIn: set Event} 
sig Category in TOP  {} 
sig Collection in TOP  { 
	isSubCollectionOf: set Collection} 
sig ComparativeRelationshipType in TOP  {} 
sig ConcreteIndividual in TOP  { 
	constitutes: set ConcreteIndividual,
	hasBeginPoint: set Instant,
	hasBeginPointInXSDDate: set date,
	hasBeginPointInXSDDateTimeStamp: set dateTimeStamp,
	hasEndPoint: set Instant,
	hasEndPointInXSDDate: set date,
	hasEndPointInXSDDateTimeStamp: set dateTimeStamp,
	hasQualityValue: set TOP,
	hasReifiedQualityValue: set QualityValue,
	historicallyDependsOn: set ConcreteIndividual} 
sig ConcreteIndividualType in TOP  {} 
sig Endurant in TOP  { 
	standsInQualifiedAttribution: set QualityValueAttributionSituation,
	standsInQualifiedConstitution: set TemporaryConstitutionSituation,
	standsInQualifiedInstantiation: set TemporaryInstantiationSituation,
	standsInQualifiedParthood: set TemporaryParthoodSituation,
	standsInQualifiedRelationship: set TemporaryRelationshipSituation,
	wasCreatedIn: set Event,
	wasTerminatedIn: set Event} 
sig EndurantType in TOP  { 
	hasAssociatedQualityValueType: set AbstractIndividualType} 
sig Event in TOP  { 
	broughtAbout: set Situation,
	isEventProperPartOf: set Event} 
sig EventType in TOP  {} 
sig ExtrinsicAspect in TOP  {} 
sig ExtrinsicMode in TOP  { 
	externallyDependsOn: set Endurant} 
sig FixedCollection in TOP  {} 
sig FunctionalComplex in TOP  {
hasComponentOf: set Object,
} 
sig Individual in TOP  {} 
sig IntrinsicAspect in TOP  {} 
sig IntrinsicMode in TOP  {} 
sig Kind in TOP  {} 
sig MaterialRelationshipType in TOP  {} 
sig Mixin in TOP  {} 
sig NonRigidType in TOP  {} 
sig NonSortal in TOP  {} 
sig Object in TOP  { 
	isCollectionMemberOf: set Collection,
	isComponentOf: set FunctionalComplex,
	isObjectProperPartOf: set Object,
	participatedIn: set Event} 
sig Participation in TOP  {} 
sig Phase in TOP  {} 
sig PhaseMixin in TOP  {} 
sig Quality in TOP  {} 
sig QualityValue in TOP  { 
	hasValueComponent: set TOP} 
sig QualityValueAttributionSituation in TOP  { 
	concernsQualityType: set EndurantType,
	concernsQualityValue: set TOP,
	concernsReifiedQualityValue: set QualityValue} 
sig Quantity in TOP  { 
	isSubQuantityOf: set Quantity} 
sig RelationshipType in TOP  {} 
sig Relator in TOP  { 
	mediates: set Endurant} 
sig RigidType in TOP  {} 
sig Role in TOP  {} 
sig RoleMixin in TOP  {} 
sig SemiRigidType in TOP  {} 
sig Situation in TOP  { 
	contributedToTrigger: set Event,
	isSituationProperPartOf: set Situation} 
sig SituationType in TOP  {} 
sig Sortal in TOP  {} 
sig SubKind in TOP  {} 
sig TemporaryConstitutionSituation in TOP  { 
	concernsConstitutedEndurant: set Endurant} 
sig TemporaryInstantiationSituation in TOP  { 
	concernsNonRigidType: set NonRigidType} 
sig TemporaryParthoodSituation in TOP  { 
	concernsTemporaryWhole: set Endurant} 
sig TemporaryRelationshipSituation in TOP  { 
	concernsRelatedEndurant: set Endurant,
	concernsRelationshipType: set RelationshipType} 
sig Type in TOP  {} 
sig VariableCollection in TOP  {} 
sig Airplane in TOP  {} 
sig Amphibious in TOP  {} 
sig Boat in TOP  {} 
sig Buyer in TOP  {} 
sig Car in TOP  {} 
sig Engine in TOP  {} 
sig Person in TOP  {} 
sig PurchasableItem in TOP  {} 
sig Purchase in TOP  { 
	involvesBuyer: set Buyer,
	involvesItem: set PurchasableItem,
	involvesSeller: set Seller} 
sig Seller in TOP  {} 
sig Vehicle in TOP  {
hasComponentVehicle: set VehiclePart} 
sig VehiclePart in TOP  { 
	isComponentOfVehicle: set Vehicle} 
sig Wheel in TOP  {} 
sig Instant in TOP  {} 

// Properties
fact {all a:Collection | a.isCollectionMemberOf in a.isObjectProperPartOf} 
fact {all r:Collection | r in Object} 
fact {all a:QualityValueAttributionSituation | a.standsInQualifiedAttribution in a.standsIn} 
fact {all r:QualityValueAttributionSituation | r in Situation} 
fact { isSubQuantityOf.isSubQuantityOf in isSubQuantityOf } 
fact { isSubCollectionOf.isSubCollectionOf in isSubCollectionOf } 
fact { isEventProperPartOf.isEventProperPartOf in isEventProperPartOf } 
fact {~mediates  & mediates in iden} 
fact { isObjectProperPartOf.isObjectProperPartOf in isObjectProperPartOf } 
fact { historicallyDependsOn.historicallyDependsOn in historicallyDependsOn } 
fact { no c1:Person, c2:Vehicle| c1 = c2} 
fact {all a:TemporaryConstitutionSituation | a.standsInQualifiedConstitution in a.standsIn} 
fact {all r:TemporaryConstitutionSituation | r in Situation} 
fact {all a:Object | a.isObjectProperPartOf in a.isProperPartOf} 
fact {all r:Object | r in TOP} 
fact { isProperPartOf.isProperPartOf in isProperPartOf } 
fact {all a:Seller | a.involvesSeller in a.mediates}
fact {all r:Seller | r in Endurant} 
fact {all a:Aspect | a.isAspectProperPartOf in a.isProperPartOf} 
fact {all r:Aspect | r in TOP} 
fact {all a:FunctionalComplex | a.isComponentOf in a.isObjectProperPartOf} 
fact {all r:FunctionalComplex | r in Object} 
fact {no iden & inheresIn} 
fact {all a:TemporaryParthoodSituation | a.standsInQualifiedParthood in a.standsIn} 
fact {all r:TemporaryParthoodSituation | r in Situation} 
fact { isAspectProperPartOf.isAspectProperPartOf in isAspectProperPartOf } 
fact {all a:PurchasableItem | a.involvesItem in a.mediates} 
fact {all r:PurchasableItem | r in Endurant} 
fact {all a:TemporaryRelationshipSituation | a.standsInQualifiedRelationship in a.standsIn} 
fact {all r:TemporaryRelationshipSituation | r in Situation} 
fact {all a:Vehicle | a.isComponentOfVehicle in a.isComponentOf} 
fact {all a:VehiclePart | a.hasComponentVehicle in a.hasComponentOf}
fact {all r:Vehicle | r in FunctionalComplex} 
fact {~inheresIn  & inheresIn in iden} 
fact {all a:TemporaryInstantiationSituation | a.standsInQualifiedInstantiation in a.standsIn} 
fact {all r:TemporaryInstantiationSituation | r in Situation} 
fact {all a:Buyer | a.involvesBuyer in a.mediates}
fact {all r:Buyer | r in Endurant} 
fact {all a:Situation | a.isSituationProperPartOf in a.isProperPartOf} 
fact {all r:Situation | r in TOP} 
fact {all a:Quantity | a.isSubQuantityOf in a.isObjectProperPartOf} 
fact {all r:Quantity | r in Object} 
fact {no iden & mediates} 
fact {all a:Collection | a.isSubCollectionOf in a.isObjectProperPartOf} 
fact {all r:Collection | r in Object} 
fact {no iden & externallyDependsOn} 
fact {all a:Event | a.isEventProperPartOf in a.isProperPartOf} 
fact {all r:Event | r in TOP} 

// gUFO Axioms 
fact { AbstractIndividual  in  (  Individual )  }
fact { AbstractIndividual  in  ( ( univ - ConcreteIndividual )  )  }
fact { AbstractIndividualType  in  (  Type )  }
fact { AbstractIndividualType  in  ( ( univ - ConcreteIndividualType )  )  }
fact { AbstractIndividualType  in  ( ( univ - RelationshipType )  )  }
fact { AntiRigidType  in  (  NonRigidType )  }
fact { AntiRigidType  in  ( ( univ - SemiRigidType )  )  }
fact { Aspect  in  (  Endurant )  }
fact { Aspect  in  ( ( univ - Object )  )  } 
fact { Aspect =   ExtrinsicAspect  +  IntrinsicAspect  }
fact { Category  in  (  NonSortal )  }
fact { Category  in  (  RigidType )  }
fact { Collection  in  (  Object )  }
fact { Collection  in  ( ( univ - FunctionalComplex )  )  }
fact { Collection  in  ( ( univ - Quantity )  )  }
fact { Collection =   FixedCollection  +  VariableCollection  }
fact { ComparativeRelationshipType  in  (  RelationshipType )  }
fact { ComparativeRelationshipType  in  ( ( univ - MaterialRelationshipType )  )  }
fact { ConcreteIndividual  in  (  Individual )  }
fact { ConcreteIndividual =   Endurant  +  Event  +  Situation  }
fact { ConcreteIndividualType  in  (  Type )  }
fact { ConcreteIndividualType  in  ( ( univ - RelationshipType )  )  }
fact { Endurant  in  (  ConcreteIndividual )  }
fact { Endurant  in  ( ( univ - Event )  )  }
fact { Endurant  in  ( ( univ - Situation )  )  } 
fact { Endurant =   Aspect  +  Object  }
fact { EndurantType  in  (  ConcreteIndividualType )  }
fact { EndurantType  in  ( ( univ - EventType )  )  }
fact { EndurantType  in  ( ( univ - SituationType )  )  }
fact { EndurantType =   NonRigidType  +  RigidType  }
fact { EndurantType =   NonSortal  +  Sortal  }
fact { Event  in  (  ConcreteIndividual )  }
fact { Event  in ( ( univ - Situation )  )  } 
fact { EventType  in  (  ConcreteIndividualType )  }
fact { EventType  in  ( ( univ - SituationType )  )  }
fact { ExtrinsicAspect  in  (  Aspect )  }
fact { ExtrinsicAspect  in  ( ( univ - IntrinsicAspect )  )  }
fact { ExtrinsicAspect =   ExtrinsicMode  +  Relator  }
fact { ExtrinsicMode  in  (   externallyDependsOn.ConcreteIndividual )  }
fact { ExtrinsicMode  in  (  ExtrinsicAspect )  }
fact { ExtrinsicMode  in  ( ( univ - Relator )  )  }
fact { ExtrinsicMode  in  ( { a : univ | #( a.(   inheresIn :> ConcreteIndividual ) ) = 1} )  }
fact { FixedCollection  in  (  Collection )  }
fact { FixedCollection  in  ( ( univ - VariableCollection )  )  }
fact { FunctionalComplex  in  (  Object )  }
fact { FunctionalComplex  in  ( ( univ - Quantity )  )  } //added
fact { Individual  in  ( ( univ - Type )  )  }
fact { Individual =   AbstractIndividual  +  ConcreteIndividual  }
fact { Instant  in  (  AbstractIndividual )  }
fact { IntrinsicAspect  in  (  Aspect )  }
fact { IntrinsicAspect  in  ( { a : univ | #( a.(   inheresIn :> ConcreteIndividual ) ) = 1} )  }
fact { IntrinsicAspect =   IntrinsicMode  +  Quality  }
fact { IntrinsicMode  in  (  IntrinsicAspect )  }
fact { IntrinsicMode  in  ( ( univ - Quality )  )  }
fact { Kind  in  (  RigidType )  }
fact { Kind  in  (  Sortal )  }
fact { Kind  in  ( ( univ - SubKind )  )  }
fact { MaterialRelationshipType  in  (  RelationshipType )  }
fact { Mixin  in  (  NonSortal )  }
fact { Mixin  in  (  SemiRigidType )  }
fact { NonRigidType  in  (  EndurantType )  }
fact { NonRigidType  in  ( ( univ - RigidType )  )  }
fact { NonRigidType =   AntiRigidType  +  SemiRigidType  }
fact { NonSortal  in  (  EndurantType )  }
fact { NonSortal  in  ( ( univ - Sortal )  )  }
fact { Object  in  (  Endurant )  }
fact { Participation  in  (  Event )  }
fact { Participation  in  ( ( ~ participatedIn.Object )  )  }
fact { Person  in  (  FunctionalComplex )  }
fact { Phase  in  (  AntiRigidType )  }
fact { Phase  in  (  Sortal )  }
fact { Phase  in  ( ( univ - Role )  )  }
fact { PhaseMixin  in  (  AntiRigidType )  }
fact { PhaseMixin  in  (  NonSortal )  }
fact { PhaseMixin  in  ( ( univ - RoleMixin )  )  }
fact { Quality  in  (  IntrinsicAspect )  }
fact { QualityValue  in  (  AbstractIndividual )  }
fact { QualityValueAttributionSituation  in  (  Situation )  }
fact { QualityValueAttributionSituation  in  ( ( ~ standsInQualifiedAttribution.Endurant )  )  }
fact { QualityValueAttributionSituation  in  ( ( univ - TemporaryConstitutionSituation )  )  }
fact { QualityValueAttributionSituation  in  ( ( univ - TemporaryInstantiationSituation )  )  }
fact { QualityValueAttributionSituation  in  ( ( univ - TemporaryParthoodSituation )  )  }
fact { QualityValueAttributionSituation  in  ( ( univ - TemporaryRelationshipSituation )  )  }
fact { QualityValueAttributionSituation  in  ( { a : univ | #( a.(   concernsQualityType :> EndurantType ) ) = 1} )  }
fact { Quantity  in  (  Object )  }
fact { RelationshipType  in  (  Type )  }
fact { Relator  in  (  ExtrinsicAspect )  }
fact { RigidType  in  (  EndurantType )  }
fact { Role  in  (  AntiRigidType )  }
fact { Role  in  (  Sortal )  }
fact { RoleMixin  in  (  AntiRigidType )  }
fact { RoleMixin  in  (  NonSortal )  }
fact { SemiRigidType  in  (  NonRigidType )  }
fact { Situation  in  (  ConcreteIndividual )  }
fact { SituationType  in  (  ConcreteIndividualType )  }
fact { Sortal  in  (  EndurantType )  }
fact { SubKind  in  (  RigidType )  }
fact { SubKind  in  (  Sortal )  }
fact { TemporaryConstitutionSituation  in  (  Situation )  }
fact { TemporaryConstitutionSituation  in  ( ( ~ standsInQualifiedConstitution.Object )  )  }
fact { TemporaryConstitutionSituation  in  ( ( univ - TemporaryInstantiationSituation )  )  }
fact { TemporaryConstitutionSituation  in  ( ( univ - TemporaryRelationshipSituation )  )  }
fact { TemporaryConstitutionSituation  in  ( { a : univ | #( a.(   concernsConstitutedEndurant :> Object ) ) = 1} )  }
fact { TemporaryInstantiationSituation  in  (  Situation )  }
fact { TemporaryInstantiationSituation  in  ( ( ~ standsInQualifiedInstantiation.Endurant )  )  }
fact { TemporaryInstantiationSituation  in  ( ( univ - TemporaryParthoodSituation )  )  }
fact { TemporaryInstantiationSituation  in  ( ( univ - TemporaryRelationshipSituation )  )  }
fact { TemporaryInstantiationSituation  in  ( { a : univ | #( a.(   concernsNonRigidType :> NonRigidType ) ) = 1} )  }
fact { TemporaryParthoodSituation  in  (  Situation )  }
fact { TemporaryParthoodSituation  in  ( ( ~ standsInQualifiedParthood.Endurant )  )  }
fact { TemporaryParthoodSituation  in  ( ( univ - TemporaryRelationshipSituation )  )  }
fact { TemporaryParthoodSituation  in  ( { a : univ | #( a.(   concernsTemporaryWhole :> Endurant ) ) = 1} )  }
fact { TemporaryRelationshipSituation  in  (   concernsRelatedEndurant.Endurant )  }
fact { TemporaryRelationshipSituation  in  (  Situation )  }
fact { TemporaryRelationshipSituation  in  ( ( ~ standsInQualifiedRelationship.Endurant )  )  }
fact { TemporaryRelationshipSituation  in  ( { a : univ | #( a.(   concernsRelationshipType :> RelationshipType ) ) = 1} )  }
fact { VariableCollection  in  (  Collection )  }

//Car Model Class Axioms
fact { Purchase  in  (  Relator )  }
fact { Purchase in  ( { a : univ | #( a.(   involvesBuyer :> Buyer ) ) >= 1} )  }
fact { Purchase in  ( { a : univ | #( a.(   involvesSeller :> Seller ) ) >= 1} )  }
fact { Purchase in  ( (  involvesItem.PurchasableItem )  )  }
fact { Buyer  in  (  Person )  }
fact { Buyer  in  ( ( ~ involvesBuyer.Purchase )  )  }
fact { Seller  in  (  Person )  }
fact { Seller  in  ( ( ~ involvesSeller.Purchase )  )  }
fact { PurchasableItem  in  (  FunctionalComplex )  }
fact { Vehicle  in  (  PurchasableItem )  }
fact { Airplane  in  (  Vehicle )  }
fact { Car  in  (  Vehicle )  }
fact { Boat  in  (  Vehicle )  }
fact { VehiclePart  in  (  PurchasableItem )  }
fact { Wheel  in  (  VehiclePart )  }
fact { Engine  in  (  VehiclePart )  }
fact { Amphibious  in  (  Car )  }
fact { Amphibious  in  (  Boat )  }
fact { Wheel in ( ( univ - Vehicle )  )  }
fact { Engine in  ( ( univ - Wheel )  )  }
fact { Engine in  ( ( univ - Person )  )  }
fact { Engine in  ( ( univ - Vehicle )  )  }
fact { Person in  ( ( univ - Wheel )  )  }
fact { Person in  ( ( univ - Vehicle )  )  }

// Other Axioms
 fact { TOP  in  (  ( univ - (   isComponentOfVehicle.( univ - Vehicle ) ) )  )  }
 fact {  isComponentOf.FunctionalComplex  in  (  Object )  }
 fact { NonRigidType  in  ( { a : univ | #( a.(   concernsNonRigidType ) ) <= 1} )  }
 fact { TOP  in  (  ( univ - (   constitutes.( univ - ConcreteIndividual ) ) )  )  }
 fact { TOP  in  (  ( univ - (   contributedToTrigger.( univ - Event ) ) )  )  }
 fact {  inheresIn.ConcreteIndividual  in  (  Aspect )  }
 fact { TOP  in  (  ( univ - (   isCollectionMemberOf.( univ - Collection ) ) )  )  }
 fact { TOP  in  (  ( univ - (   isEventProperPartOf.( univ - Event ) ) )  )  }
 fact { ConcreteIndividual  in  ( { a : univ | #( a.(   inheresIn ) ) <= 1} )  }
 fact { RelationshipType  in  ( { a : univ | #( a.(   concernsRelationshipType ) ) <= 1} )  }
 fact {  concernsRelationshipType.RelationshipType  in  (  TemporaryRelationshipSituation )  }
 fact { TOP  in  (  ( univ - (   concernsQualityType.( univ - EndurantType ) ) )  )  }
 fact { TOP  in  (  ( univ - (   concernsRelatedEndurant.( univ - Endurant ) ) )  )  }
 fact {  mediates.Endurant  in  (  Relator )  }
 fact {  historicallyDependsOn.ConcreteIndividual  in  (  ConcreteIndividual )  }
 fact { TOP  in  (  ( univ - (   externallyDependsOn.( univ - Endurant ) ) )  )  }
 fact {  constitutes.ConcreteIndividual  in  (  ConcreteIndividual )  }
 fact { TOP  in  (  ( univ - (   isSituationProperPartOf.( univ - Situation ) ) )  )  }
 fact {  wasTerminatedIn.Event  in  (  Endurant )  }
 fact { Endurant  in  ( { a : univ | #( a.(   concernsTemporaryWhole ) ) <= 1} )  }
 fact {  concernsTemporaryWhole.Endurant  in  (  TemporaryParthoodSituation )  }
 fact {  concernsRelatedEndurant.Endurant  in  (  TemporaryRelationshipSituation )  }
 fact {  hasValueComponent.TOP  in  (  QualityValue )  }
 fact { EndurantType  in  ( { a : univ | #( a.(   concernsQualityType ) ) <= 1} )  }
 fact { TOP  in  (  ( univ - (   involvesItem.( univ - PurchasableItem ) ) )  )  }
 fact { TOP  in  (  ( univ - (   hasEndPoint.( univ - Instant ) ) )  )  }
 fact {  contributedToTrigger.Event  in  (  Situation )  }
 fact {  manifestedIn.Event  in  (  Aspect )  }
 fact { TOP  in  (  ( univ - (   historicallyDependsOn.( univ - ConcreteIndividual ) ) )  )  }
 fact {  isObjectProperPartOf.Object  in  (  Object )  }
 fact {  concernsReifiedQualityValue.QualityValue  in  (  QualityValueAttributionSituation )  }
 fact { TOP  in  (  ( univ - (   mediates.( univ - Endurant ) ) )  )  }
 fact {  hasQualityValue.TOP  in  (  ConcreteIndividual )  }
 fact {  concernsConstitutedEndurant.Endurant  in  (  TemporaryConstitutionSituation )  }
 fact { TOP  in  (  ( univ - (   hasReifiedQualityValue.( univ - QualityValue ) ) )  )  }
 fact { TOP  in  (  ( univ - (   concernsTemporaryWhole.( univ - Endurant ) ) )  )  }
 fact {  isComponentOfVehicle.Vehicle  in  (  VehiclePart )  }
 fact {  isAspectProperPartOf.Aspect  in  (  Aspect )  }
 fact { TOP  in  (  ( univ - (   isComponentOf.( univ - FunctionalComplex ) ) )  )  }
 fact {  hasReifiedQualityValue.QualityValue  in  (  ConcreteIndividual )  }
 fact { TOP  in  (  ( univ - (   wasCreatedIn.( univ - Event ) ) )  )  }
 fact { TOP  in  (  ( univ - (   isAspectProperPartOf.( univ - Aspect ) ) )  )  }
 fact { TOP  in  (  ( univ - (   involvesSeller.( univ - Seller ) ) )  )  }
 fact {  hasBeginPoint.Instant  in  (  ConcreteIndividual )  }
 fact { TOP  in  (  ( univ - (   isObjectProperPartOf.( univ - Object ) ) )  )  }
 fact {  participatedIn.Event  in  (  Object )  }
 fact { TOP  in  (  ( univ - (   manifestedIn.( univ - Event ) ) )  )  }
 fact {  concernsNonRigidType.NonRigidType  in  (  TemporaryInstantiationSituation )  }
 fact { TOP  in  (  ( univ - (   hasAssociatedQualityValueType.( univ - AbstractIndividualType ) ) )  )  }
 fact {  broughtAbout.Situation  in  (  Event )  }
 fact {  concernsQualityValue.TOP  in  (  QualityValueAttributionSituation )  }
 fact { TOP  in  (  ( univ - (   isSubCollectionOf.( univ - Collection ) ) )  )  }
 fact { TOP  in  (  ( univ - (   wasTerminatedIn.( univ - Event ) ) )  )  }
 fact { TOP  in  (  ( univ - (   participatedIn.( univ - Event ) ) )  )  }
 fact {  concernsQualityType.EndurantType  in  (  QualityValueAttributionSituation )  }
 fact {  hasAssociatedQualityValueType.AbstractIndividualType  in  (  EndurantType )  }
 fact {  hasEndPoint.Instant  in  (  ConcreteIndividual )  }
 fact {  involvesBuyer.Buyer  in  (  Purchase )  }
 fact { TOP  in  (  ( univ - (   concernsNonRigidType.( univ - NonRigidType ) ) )  )  }
 fact { TOP  in  (  ( univ - (   isSubQuantityOf.( univ - Quantity ) ) )  )  }
 fact { TOP  in  (  ( univ - (   hasBeginPoint.( univ - Instant ) ) )  )  }
 fact {  isEventProperPartOf.Event  in  (  Event )  }
 fact {  externallyDependsOn.Endurant  in  (  ExtrinsicMode )  }
 fact { Endurant  in  ( { a : univ | #( a.(   concernsRelatedEndurant ) ) <= 1} )  }
 fact { TOP  in  (  ( univ - (   inheresIn.( univ - ConcreteIndividual ) ) )  )  }
 fact {  wasCreatedIn.Event  in  (  Endurant )  }
 fact { TOP  in  (  ( univ - (   concernsReifiedQualityValue.( univ - QualityValue ) ) )  )  }
 fact {  isSituationProperPartOf.Situation  in  (  Situation )  }
 fact {  involvesSeller.Seller  in  (  Purchase )  }
 fact {  isSubQuantityOf.Quantity  in  (  Quantity )  }
 fact { QualityValue  in  ( { a : univ | #( a.(   concernsReifiedQualityValue ) ) <= 1} )  }
 fact { TOP  in  (  ( univ - (   broughtAbout.( univ - Situation ) ) )  )  }
 fact { TOP  in  (  ( univ - (   concernsConstitutedEndurant.( univ - Endurant ) ) )  )  }
 fact { TOP  in  (  ( univ - (   involvesBuyer.( univ - Buyer ) ) )  )  }
 fact {  involvesItem.PurchasableItem  in  (  Purchase )  }
 fact {  isSubCollectionOf.Collection  in  (  Collection )  }
 fact {  isCollectionMemberOf.Collection  in  (  Object )  }
 fact { TOP  in  (  ( univ - (   concernsRelationshipType.( univ - RelationshipType ) ) )  )  }

sig dateTime {}
sig date {}
sig dateTimeStamp {}

run {

	TOP = Purchase + Buyer + Seller + PurchasableItem + Vehicle + Car + Boat + Airplane + VehiclePart + Engine + Wheel + Amphibious
	
	isProperPartOf=isObjectProperPartOf
	isObjectProperPartOf=isComponentOf
	isComponentOf = isComponentOfVehicle
	mediates = involvesBuyer + involvesSeller + involvesItem

	#broughtAbout=0
	#categorizes=0
	#constitutes=0	
	#contributedToTrigger=0
	#hasReifiedQualityValue=0
	#historicallyDependsOn=0
	#inheresIn=0
	#isSubQuantityOf=0
	#isSubCollectionOf=0
	#isCollectionMemberOf=0
	#isAspectProperPartOf=0
	#manifestedIn=0
	#participatedIn=0
	#externallyDependsOn=0
	#partitions=0
	#hasQualityValue=0
	
	#hasEndPoint=0
	#hasBeginPoint=0
	#date=0
	#dateTime=0
	#dateTimeStamp=0

	// Rules that I needed to add but we did not plan on identifying
	no isProperPartOf & iden
	all x: Vehicle | #(isComponentOfVehicle.x) >= 2
	all x: VehiclePart | #(x.isComponentOfVehicle) = 1
	VehiclePart = Engine + Wheel
	PurchasableItem = Vehicle + VehiclePart

	// 1st rule that should be learned: Missing complete generation set
	Vehicle  = Car + Airplane + Boat
	
	// 2nd rule that should be learned: Amphibious = intersection between Boat and Car
	Amphibious = Boat & Car

	// 3rd rule that should be learned: Every vehicle has an engine
	all x:Vehicle | some (isComponentOfVehicle.x):>Engine
	
	// 4th rule that should be learned: every car has 4 wheels
	all x: Car | #(isComponentOfVehicle.x):>Wheel=4
	
	// To generate a couter example for each rule, do:
	// not (rule), as in:
	// not (all x: Car | #(isComponentOfVehicle.x):>Wheel=4)
	// Then adjust the class cardinalities below if necessary
	// I suggest negating one rule at a time to generate examples that only break one rule,
	// thus facilitating the learning process
	// It may be necessary to force the existence of the classes using the expressions below:
	
	#Vehicle>0
	#Car>0
	#Purchase=0
	#Person=0
	
} for 6

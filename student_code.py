import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        #count_fact = len(fact_or_rule.supports_facts)
        #count_rule = len(fact_or_rule.supports_rules) 
        #index = self.facts.index(fact_or_rule)
        #if (fact_or_rule.asserted == True) and (len(fact_or_rule.supported_by) == 0):
        #    del(self.facts[index])
        #elif (fact_or_rule.asserted == False):
        #    for i in range(0, count_fact):
        #        supported_fact = fact_or_rule.supports_facts[i]
        #        if (len(supported_fact.supported_by) == 1):
        #            index_of_supported_fact = self.facts.index(supported_fact)
        #            del(self.facts[index])
        #            del(self.facts[index_of_supported_fact])
        #        else:
        #            del(self.facts[index])
        #    for i in range(0, count_rule):
        #        supported_rule = fact_or_rule.supports_rules[i]
        #        if (len(supported_rule.supported_by) == 1):
        #            index_of_supported_rule = self.rules.index(supported_rule)
        #            del(self.facts[index])
        #            del(self.rules[index_of_supported_rule])
        #        else:
        #            del(self.facts[index])

        
        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        count = len(rule.lhs)
        lhs = []
        rhs = []
        if (count == 1):
            bindings = match(rule.lhs[0], fact.statement)
            if type(bindings) is not bool:
                print(rule.rhs)
                new_statement = instantiate(rule.rhs, bindings)
                new_fact = Fact(new_statement)
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
                new_fact.supported_by.append((fact, rule))
                print(rule)
                kb.rules.append(rule)
        else:
            for i in range(1, count):
                bindings = match(rule.lhs[i], fact.statement)
                if type(bindings) is not bool:
                    lhs.append(instantiate(rule.lhs[i], bindings))
                brhs = match(rule.rhs, fact.statement)
                if type(brhs) is not bool:
                    rhs.append(instantiate(rule.rhs, brhs))
                new_rule = Rule([lhs, rhs])
                rule.supports_rules.append(new_rule)
                fact.supports_rules.append(new_rule)
                new_rule.supported_by.append((fact, rule))
                print(new_rule)
                kb.rules.append(new_rule)





        #binding = match(rule.lhs[0], fact.statement)
        #if type(binding) is not bool:
        #    new_fact =  Fact(instantiate(rule.lhs[0], binding))
        #    print(new_fact)
            #print(rule.rhs)
            #rule.supported_by.append(fact)
        #    #fact.supports_rules.append(rule)
        #    kb.rules.append(new_fact)    

                


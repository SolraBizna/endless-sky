/* ConditionSet.cpp
Copyright (c) 2014 by Michael Zahniser

Endless Sky is free software: you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later version.

Endless Sky is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU General Public License for more details.
*/

#include "ConditionSet.h"

#include "DataNode.h"
#include "DataWriter.h"
#include "Files.h"
#include "Random.h"

#include <algorithm>
#include <cmath>
#include <limits>
#include <set>

using namespace std;

namespace {
	typedef int64_t (*BinFun)(int64_t, int64_t);
	BinFun Op(const string &op)
	{
		// This map defines functions that each "operator" should be mapped to.
		// In each function "a" is the condition's current value and "b" is the
		// integer value given as the other argument of the operator.
		// Test operators return 0 (false) or 1 (true).
		// "Apply" operators return the value that the condition should have
		// after applying the expression.
		static const map<string, BinFun> opMap = {
			{"==", [](int64_t a, int64_t b) -> int64_t { return a == b; }},
			{"!=", [](int64_t a, int64_t b) -> int64_t { return a != b; }},
			{"<", [](int64_t a, int64_t b) -> int64_t { return a < b; }},
			{">", [](int64_t a, int64_t b) -> int64_t { return a > b; }},
			{"<=", [](int64_t a, int64_t b) -> int64_t { return a <= b; }},
			{">=", [](int64_t a, int64_t b) -> int64_t { return a >= b; }},
			{"=", [](int64_t a, int64_t b) { return b; }},
			{"*=", [](int64_t a, int64_t b) { return a * b; }},
			{"+=", [](int64_t a, int64_t b) { return a + b; }},
			{"-=", [](int64_t a, int64_t b) { return a - b; }},
			{"/=", [](int64_t a, int64_t b) { return b ? a / b : numeric_limits<int64_t>::max(); }},
			{"<?=", [](int64_t a, int64_t b) { return min(a, b); }},
			{">?=", [](int64_t a, int64_t b) { return max(a, b); }},
			{"%", [](int64_t a, int64_t b) { return (a % b); }},
			{"*", [](int64_t a, int64_t b) { return a * b; }},
			{"+", [](int64_t a, int64_t b) { return a + b; }},
			{"-", [](int64_t a, int64_t b) { return a - b; }},
			{"/", [](int64_t a, int64_t b) { return b ? a / b : numeric_limits<int64_t>::max(); }},
			{"&=", [](int64_t a, int64_t b) { return a & b; }},
			{"|=", [](int64_t a, int64_t b) { return a | b; }},
			{"~=", [](int64_t a, int64_t b) { return a ^ b; }},
			{">>=", [](int64_t a, int64_t b) { return a >> b; }},
			{"<<=", [](int64_t a, int64_t b) { return a << b; }},
			{"&", [](int64_t a, int64_t b) { return a & b; }},
			{"|", [](int64_t a, int64_t b) { return a | b; }},
			{"~", [](int64_t a, int64_t b) { return a ^ b; }},
			{">>", [](int64_t a, int64_t b) { return a >> b; }},
			{"<<", [](int64_t a, int64_t b) { return a << b; }},
		};
		
		auto it = opMap.find(op);
		return (it != opMap.end() ? it->second : nullptr);
	}
	
	// Indicate if the operation is a comparison or modifies the condition.
	bool IsComparison(const string &op)
	{
		static const set<string> comparison = {
			"==", "!=", "<", ">", "<=", ">="
		};
		return comparison.count(op);
	}
	
	bool IsAssignment(const string &op)
	{
		static const set<string> assignment = {
			"=", "+=", "-=", "*=", "/=", "<?=", ">?=",
			"&=", "|=", "^=", ">>=", "<<=",
		};
		return assignment.count(op);
	}
	
	bool IsSimple(const string &op)
	{
		static const set<string> simple = {
			"(", ")", "[", "]", "+", "-", "*", "/", "%",
			"&", "|", "^", ">>", "<<",
		};
		return simple.count(op);
	}
	
	int Precedence(const string &op)
	{
		static const map<string, int> precedence = {
			{"(", 0}, {")", 0},
			{"[", 0}, {"]", 0},
			// Using the C precedence for bitwise operations, even though it
			// is usually NOT what is wanted.
			{"&", 1}, {"|", 1}, {"~", 1},
			{"<<", 2}, {">>", 2},
			{"+", 3}, {"-", 3},
			{"*", 4}, {"/", 4}, {"%", 4}
		};
		return precedence.at(op);
	}
	
	// Test to determine if unsupported operations are requested.
	bool HasInvalidOperators(const vector<string> &tokens)
	{
		static const set<string> invalids = {
			"{", "}", "!", "^", "||", "&&",
		};
		for(const string &str : tokens)
			if(invalids.count(str))
				return true;
		return false;
	}
	
	// Ensure the ConditionSet line has balanced parentheses on both sides.
	bool HasUnbalancedParentheses(const vector<string> &tokens)
	{
		vector<char> parentheses;
		for(const string &str : tokens)
		{
			if(!parentheses.empty() && (IsAssignment(str) || IsComparison(str)))
				return true;
			else if(str == "(")
				parentheses.push_back('(');
			else if(str == ")") {
				if(parentheses.empty())
					return true;
				else if(parentheses.back() != '(')
					return true;
				parentheses.pop_back();
			}
			else if(str == "[")
				parentheses.push_back('[');
			else if(str == "]") {
				if(parentheses.empty())
					return true;
				else if(parentheses.back() != '[')
					return true;
				parentheses.pop_back();
			}
		}
		return !parentheses.empty();
	}
	
	// Perform a preliminary assessment of the input condition, to determine if it is remotely well-formed.
	// The final assessment of its validity will be whether it parses into an evaluable Expression.
	bool IsValidCondition(const DataNode &node)
	{
		const vector<string> &tokens = node.Tokens();
		int assigns = count_if(tokens.begin(), tokens.end(), IsAssignment);
		int compares = count_if(tokens.begin(), tokens.end(), IsComparison);
		if(assigns + compares != 1)
			node.PrintTrace("An expression must either perform a comparison, or an assign a value:");
		else if(HasInvalidOperators(tokens))
			node.PrintTrace("Braces, exponentiation, and boolean math are not supported:");
		else if(HasUnbalancedParentheses(tokens))
			node.PrintTrace("Unbalanced parentheses or brackets in condition expression:");
		else if(count_if(tokens.begin(), tokens.end(), [](const string &token)
				{ return token.size() > 1 && token.front() == '('; }))
			node.PrintTrace("Parentheses must be separate from tokens:");
		else
			return true;
		// (Do not test for embedded brackets in tokens, as there are several
		// ways this is useful.)
		
		return false;
	}
	
	bool UsedAll(const vector<bool> &status)
	{
		for(auto v : status)
			if(!v)
				return false;
		return true;
	}
	
	// Finding the left operand's index if getLeft = true. The operand's index is the first non-empty, non-used index.
	size_t FindOperandIndex(const vector<string> &tokens, const vector<string> &operators, const vector<int> &resultIndices, const size_t &opIndex, bool getLeft)
	{
		// Start at the operator index (left), or just past it (right).
		size_t index = opIndex + !getLeft;
		if(getLeft)
		{
			while(tokens.at(index).empty() && index > 0)
				--index;
			if(index > 0 && operators.at(index) == "]")
			{
				int balance = 1;
				while(index > 0 && balance > 0)
				{
					if(operators.at(index) == "(" || operators.at(index) == "[")
						--balance;
					else if(operators.at(index) == ")" || operators.at(index) == "]")
						++balance;
					--index;
				}
			}
		}
		else
			while(tokens.at(index).empty() && index < tokens.size() - 2)
				++index;
		// Trace any used data to find the latest result.
		while(resultIndices.at(index) > 0)
			index = resultIndices.at(index);
		
		return index;
	}
	
	void PrintConditionError(const vector<string> &side)
	{
		string message = "Error decomposing complex condition expression:\nFound:\t";
		for(const string &str : side)
			message += " \"" + str + "\"";
		Files::LogError(message);
	}
	
	bool IsUnrepresentable(const string &token)
	{
		if(DataNode::IsNumber(token))
		{
			auto value = DataNode::Value(token);
			if(value > static_cast<double>(numeric_limits<int64_t>::max()) ||
					value < static_cast<double>(numeric_limits<int64_t>::min()))
				return true;
		}
		// It's possible that a condition uses purely representable values, but performs math
		// that result in unrepresentable values. However, that situation cannot be detected
		// during expression construction, only during execution.
		return false;
	}

	bool IsValidLvalue(const vector<string> &lhs)
	{
		if(lhs.size() == 1)
			return true; // A single token
		else if(lhs.size() > 3 && lhs.at(1) == "[" && lhs.back() == "]")
			return true; // A bracket expression
		else
			return false; // Something weird
	}
}



// Construct and Load() at the same time.
ConditionSet::ConditionSet(const DataNode &node)
{
	Load(node);
}



// Load a set of conditions from the children of this node.
void ConditionSet::Load(const DataNode &node)
{
	isOr = (node.Token(0) == "or");
	for(const DataNode &child : node)
		Add(child);
}



// Save a set of conditions.
void ConditionSet::Save(DataWriter &out) const
{
	for(const Expression &expression : expressions)
		expression.Save(out);
	
	for(const ConditionSet &child : children)
	{
		out.Write(child.isOr ? "or" : "and");
		out.BeginChild();
		{
			child.Save(out);
		}
		out.EndChild();
	}
}



// Check if there are any entries in this set.
bool ConditionSet::IsEmpty() const
{
	return expressions.empty() && children.empty();
}



// Read a single condition from a data node.
void ConditionSet::Add(const DataNode &node)
{
	// Special keywords have a node size of 1 (never, and, or), or 2 (unary operators).
	// Simple conditions have a node size of 3, while complex conditions feature a single
	// non-simple operator (e.g. <=) and any number of simple operators.
	static const string UNRECOGNIZED = "Unrecognized condition expression:";
	static const string UNREPRESENTABLE = "Unrepresentable condition value encountered";
	if(node.Size() == 2)
	{
		if(IsUnrepresentable(node.Token(1)))
			node.PrintTrace(UNREPRESENTABLE);
		else if(!Add(node.Token(0), node.Token(1)))
			node.PrintTrace(UNRECOGNIZED);
	}
	else if(node.Size() == 1 && node.Token(0) == "never")
		expressions.emplace_back("'", "!=", "0");
	else if(node.Size() == 1 && (node.Token(0) == "and" || node.Token(0) == "or"))
	{
		// The "and" and "or" keywords introduce a nested condition set.
		children.emplace_back(node);
		// If a child node has assignment operators, warn on load since
		// these will be processed after all non-child expressions.
		if(children.back().hasAssign)
			node.PrintTrace("Assignment expressions contained within and/or groups are applied last. This may be unexpected.");
	}
	else if(IsValidCondition(node))
	{
		// This is a valid condition containing a single assignment or comparison operator.
		if(node.Size() == 3)
		{
			if(IsUnrepresentable(node.Token(0)) || IsUnrepresentable(node.Token(2)))
				node.PrintTrace(UNREPRESENTABLE);
			else if(!Add(node.Token(0), node.Token(1), node.Token(2)))
				node.PrintTrace(UNRECOGNIZED);
		}
		else
		{
			// Split the DataNode into left- and right-hand sides.
			auto lhs = vector<string>();
			auto rhs = vector<string>();
			string op;
			for(const string &token : node.Tokens())
			{
				if(IsUnrepresentable(token))
				{
					node.PrintTrace(UNREPRESENTABLE);
					return;
				}
				else if(!op.empty())
					rhs.emplace_back(token);
				else if(IsComparison(token))
					op = token;
				else if(IsAssignment(token))
				{
					if(IsValidLvalue(lhs))
						op = token;
					else
					{
						node.PrintTrace("The left hand side of an assignment must be a single token or a bracket expression:");
						return;
					}
				}
				else
					lhs.emplace_back(token);
			}
			if(!Add(lhs, op, rhs))
				node.PrintTrace(UNRECOGNIZED);
		}
	}
	if(!expressions.empty() && expressions.back().IsEmpty())
	{
		node.PrintTrace("Condition parses to an empty set:");
		expressions.pop_back();
	}
}



// Add a unary operator line to the list of expressions.
bool ConditionSet::Add(const string &firstToken, const string &secondToken)
{
	// Each "unary" operator can be mapped to an equivalent binary expression.
	if(firstToken == "not")
		expressions.emplace_back(secondToken, "==", "0");
	else if(firstToken == "has")
		expressions.emplace_back(secondToken, "!=", "0");
	else if(firstToken == "set")
		expressions.emplace_back(secondToken, "=", "1");
	else if(firstToken == "clear")
		expressions.emplace_back(secondToken, "=", "0");
	else if(secondToken == "++")
		expressions.emplace_back(firstToken, "+=", "1");
	else if(secondToken == "--")
		expressions.emplace_back(firstToken, "-=", "1");
	else
		return false;
	
	hasAssign |= !expressions.back().IsTestable();
	return true;
}



// Add a simple condition expression to the list of expressions.
bool ConditionSet::Add(const string &name, const string &op, const string &value)
{
	// If the operator is recognized, map it to a binary function.
	BinFun fun = Op(op);
	if(!fun)
		return false;
	
	hasAssign |= !IsComparison(op);
	expressions.emplace_back(name, op, value);
	return true;
}



// Add a complex condition expression to the list of expressions.
bool ConditionSet::Add(const vector<string> &lhs, const string &op, const vector<string> &rhs)
{
	BinFun fun = Op(op);
	if(!fun)
		return false;
	
	hasAssign |= !IsComparison(op);
	expressions.emplace_back(lhs, op, rhs);
	return true;
}



// Check if the given condition values satify this set of conditions. Performs any assignments
// on a temporary condition map, if this set mixes comparisons and modifications.
bool ConditionSet::Test(const Conditions &conditions) const
{
	// If this ConditionSet contains any expressions with operators that
	// modify the condition map, then they must be applied before testing,
	// to generate any temporary conditions needed.
	Conditions created;
	if(hasAssign)
		TestApply(conditions, created);
	return TestSet(conditions, created);
}



// Modify the given set of conditions.
void ConditionSet::Apply(Conditions &conditions) const
{
	Conditions unused;
	for(const Expression &expression : expressions)
		if(!expression.IsTestable())
			expression.Apply(conditions, unused);
	
	for(const ConditionSet &child : children)
		child.Apply(conditions);
}



// Check if this set is satisfied by either the created, temporary conditions, or the given conditions.
bool ConditionSet::TestSet(const Conditions &conditions, const Conditions &created) const
{
	// Not all expressions may be testable: some may have been used to form the "created" condition map.
	for(const Expression &expression : expressions)
		if(expression.IsTestable())
		{
			bool result = expression.Test(conditions, created);
			// If this is a set of "and" conditions, bail out as soon as one of them
			// returns false. If it is an "or", bail out if anything returns true.
			if(result == isOr)
				return result;
		}
	
	for(const ConditionSet &child : children)
	{
		bool result = child.TestSet(conditions, created);
		if(result == isOr)
			return result;
	}
	// If this is an "and" condition, all the above conditions were true, so return
	// true. If it is an "or," no condition returned true, so return false.
	return !isOr;
}



// Construct new, temporary conditions based on the assignment expressions in
// this ConditionSet and the values in the player's conditions map.
void ConditionSet::TestApply(const Conditions &conditions, Conditions &created) const
{
	for(const Expression &expression : expressions)
		if(!expression.IsTestable())
			expression.TestApply(conditions, created);
	
	for(const ConditionSet &child : children)
		child.TestApply(conditions, created);
}



// Constructor for complex expressions.
ConditionSet::Expression::Expression(const vector<string> &left, const string &op, const vector<string> &right)
	: op(op), fun(Op(op)), left(left), right(right)
{
}



// Constructor for simple expressions.
ConditionSet::Expression::Expression(const string &left, const string &op, const string &right)
	: op(op), fun(Op(op)), left(left), right(right)
{
}



void ConditionSet::Expression::Save(DataWriter &out) const
{
	for(const string &str : left.ToStrings())
		out.WriteToken(str);
	out.WriteToken(op);
	for(const string &str : right.ToStrings())
		out.WriteToken(str);
	out.Write();
}



// Create a loggable string (for PrintTrace).
string ConditionSet::Expression::ToString() const
{
	return left.ToString() + " \"" + op + "\" " + right.ToString();
}



// Checks if either side of the expression is tokenless.
bool ConditionSet::Expression::IsEmpty() const
{
	return left.IsEmpty() || right.IsEmpty();
}



// Returns everything to the left of the main assignment or comparison operator.
// In an assignment expression, this should be only a single token.
string ConditionSet::Expression::Name() const
{
	return left.ToString();
}



// Returns true if the operator is a comparison and false otherwise.
bool ConditionSet::Expression::IsTestable() const
{
	return IsComparison(op);
}



// Evaluate both the left- and right-hand sides of the expression, then compare the evaluated numeric values.
bool ConditionSet::Expression::Test(const Conditions &conditions, const Conditions &created) const
{
	int64_t lhs = left.Evaluate(conditions, created);
	int64_t rhs = right.Evaluate(conditions, created);
	return fun(lhs, rhs);
}



// Assign the computed value to the desired condition.
void ConditionSet::Expression::Apply(Conditions &conditions, Conditions &created) const
{
	int64_t &c = conditions[left.GetConditionName(conditions, created)];
	int64_t value = right.Evaluate(conditions, created);
	c = fun(c, value);
}



// Assign the computed value to the desired temporary condition.
void ConditionSet::Expression::TestApply(const Conditions &conditions, Conditions &created) const
{
	int64_t &c = created[left.GetConditionName(conditions, created)];
	int64_t value = right.Evaluate(conditions, created);
	c = fun(c, value);
}



// Constructor for one side of a complex expression (supports multiple simple operators and parentheses).
ConditionSet::Expression::SubExpression::SubExpression(const vector<string> &side)
{
	if(side.empty())
		return;
	
	ParseSide(side);
	GenerateSequence();
}



// Simple condition constructor. For legacy support of the 'never' condition,
// replace the empty string argument with a bare quote.
ConditionSet::Expression::SubExpression::SubExpression(const string &side)
{
	tokens.emplace_back(side.empty() ? "'" : side);
}



// Special constructor used only for SubExpressions within SubExpressions.
ConditionSet::Expression::SubExpression::SubExpression(vector<string>::const_iterator tokensBegin,
													   vector<string>::const_iterator operatorsBegin,
													   vector<string>::const_iterator operatorsEnd) {
	tokens.push_back(*tokensBegin++);
	while(operatorsBegin != operatorsEnd) {
		operators.push_back(*operatorsBegin++);
		tokens.push_back(*tokensBegin++);
	}
	GenerateSequence();
}



// Convert the tokens and operators back to a string, for use in logging.
const string ConditionSet::Expression::SubExpression::ToString() const
{
	string out;
	static const string SPACE = " ";
	size_t i = 0;
	for( ; i < operators.size(); ++i)
	{
		if(!tokens[i].empty())
		{
			out += tokens[i];
			out += SPACE;
		}
		out += operators[i];
		if(i != operators.size() - 1)
			out += SPACE;
	}
	// The tokens vector contains more values than the operators vector.
	for( ; i < tokens.size(); ++i)
	{
		if(i != 0)
			out += SPACE;
		out += tokens[i];
	}
	return out;
}



// Interleave the tokens and operators, for use in the save file.
const vector<string> ConditionSet::Expression::SubExpression::ToStrings() const
{
	auto out = vector<string>();
	out.reserve(tokens.size() + operators.size());
	size_t i = 0;
	for( ; i < operators.size(); ++i)
	{
		if(!tokens[i].empty())
			out.emplace_back(tokens[i]);
		out.emplace_back(operators[i]);
	}
	for( ; i < tokens.size(); ++i)
		if(!tokens[i].empty())
			out.emplace_back(tokens[i]);
	return out;
}


// Check if this SubExpression was able to build correctly.
bool ConditionSet::Expression::SubExpression::IsEmpty() const
{
	return tokens.empty();
}



// Evaluate the SubExpression using the given condition maps.
int64_t ConditionSet::Expression::SubExpression::Evaluate(const Conditions &conditions, const Conditions &created) const
{
	// Sanity check.
	if(tokens.empty())
		return 0;
	
	// For SubExpressions with no Operations (i.e. simple conditions), tokens will consist
	// of only the condition or numeric value to be returned as-is after substitution.
	auto data = SubstituteValues(tokens, conditions, created);
	
	if(!sequence.empty())
	{
		// Each Operation adds to the end of the data vector.
		data.reserve(operatorCount + data.size());
		for(const Operation &op : sequence)
			data.emplace_back(op.fun(data[op.a], data[op.b]));
	}
	
	return data.back();
}



// Parse the input vector into the tokens and operators vectors. Parentheses are
// considered simple operators, and also insert an empty string into tokens.
void ConditionSet::Expression::SubExpression::ParseSide(const vector<string> &side)
{
	static const string EMPTY;
	int parentheses = 0;
	// Construct the tokens and operators vectors.
	for(size_t i = 0; i < side.size(); ++i)
	{
		if(side[i] == "(" || side[i] == ")" || side[i] == "]")
		{
			// Ensure reconstruction by adding a blank token.
			tokens.emplace_back(EMPTY);
			operators.emplace_back(side[i]);
			++parentheses;
		}
		else if(side[i] == "[")
		{
			if(tokens.empty() || tokens.back() == EMPTY)
			{
				PrintConditionError(side);
				tokens.clear();
				operators.clear();
				return; // !!!
			}
			// (Left brackets don't need blank tokens.)
			operators.emplace_back(side[i]);
			++parentheses;
			++operatorCount;
		}
		else if(IsSimple(side[i]))
		{
			// Normal operators do not need a token insertion.
			operators.emplace_back(side[i]);
			++operatorCount;
		}
		else
			tokens.emplace_back(side[i]);
	}
	
	if(tokens.empty() || !operatorCount)
		operators.clear();
	else if(parentheses % 2 != 0)
	{
		// This should have been caught earlier, but just in case.
		PrintConditionError(side);
		tokens.clear();
		operators.clear();
	}
	// Remove empty strings that wrap simple conditions, so any token
	// wrapped by only parentheses simplifies to just the token.
	if(operators.empty() && !tokens.empty())
		tokens.erase(remove_if(tokens.begin(), tokens.end(),
			[](const string &token) { return token.empty(); }), tokens.end());
}



// Parse the token and operators vectors to make the sequence vector.
void ConditionSet::Expression::SubExpression::GenerateSequence()
{
	// Simple conditions have only a single token and no operators.
	if(tokens.empty() || operators.empty())
		return;
	// Use a boolean vector to indicate when an operator has been used.
	auto usedOps = vector<bool>(operators.size(), false);
	// Read the operators vector just once by using a stack.
	auto opStack = vector<size_t>();
	// Store the data index for each Operation, for use by later Operations.
	size_t destinationIndex = tokens.size();
	auto dataDest = vector<int>(destinationIndex + operatorCount, -1);
	size_t opIndex = 0;
	while(!UsedAll(usedOps))
	{
		while(true)
		{
			// Before anything else... have we reached a bracket?
			if(operators.at(opIndex) == "[") {
				// Index for the subexpression result to be substituted at
				size_t modIndex = opIndex;
				int balance = 1;
				// Consume the open bracket
				usedOps.at(opIndex++) = true;
				// Consume everything up to the next close bracket
				while(balance > 0 && opIndex < operators.size()) {
					if(operators.at(opIndex) == "(" || operators.at(opIndex) == "[")
						++balance;
					else if(operators.at(opIndex) == ")" || operators.at(opIndex) == "]")
						--balance;
					dataDest.at(opIndex) = modIndex;
					usedOps.at(opIndex++) = true;
				}
				if(balance != 0)
				{
					Files::LogError("Did not find matched brackets:");
					PrintConditionError(ToStrings());
					tokens.clear();
					operators.clear();
					sequence.clear();
					return;
				}
				SubExpression subExpression(tokens.cbegin() + modIndex + 1,
											operators.cbegin() + modIndex + 1,
											operators.cbegin() + opIndex - 1);
				bracketExpressions.emplace_back(modIndex, move(subExpression));
				if(opIndex >= operators.size())
					break;
				else
					continue;
			}
			// Stack ops until one of lower or equal precedence is found, then evaluate the higher one first.
			if(opStack.empty() || operators.at(opIndex) == "("
					|| (Precedence(operators.at(opIndex)) > Precedence(operators.at(opStack.back()))))
			{
				opStack.push_back(opIndex);
				// Mark this operator as used and advance.
				usedOps.at(opIndex++) = true;
				break;
			}
			
			size_t workingIndex = opStack.back();
			opStack.pop_back();
			
			// A left parentheses results in a no-op step.
			if(operators.at(workingIndex) == "(")
			{
				if(operators.at(opIndex) != ")")
				{
					Files::LogError("Did not find matched parentheses:");
					PrintConditionError(ToStrings());
					tokens.clear();
					operators.clear();
					sequence.clear();
					return;
				}
				// "Use" the parentheses and advance operators.
				usedOps.at(opIndex++) = true;
				break;
			}
			else if(!AddOperation(dataDest, destinationIndex, workingIndex))
				return;
		}
	}
	// Handle remaining operators (which cannot be parentheses).
	while(!opStack.empty())
	{
		size_t workingIndex = opStack.back();
		opStack.pop_back();
		
		if(operators.at(workingIndex) == "(" || operators.at(workingIndex) == ")"
			|| operators.at(workingIndex) == "]")
		{
			Files::LogError("Mismatched parentheses or brackets:" + ToString());
			tokens.clear();
			operators.clear();
			sequence.clear();
			return;
		}
		else if(!AddOperation(dataDest, destinationIndex, workingIndex))
			return;
	}
	// All operators and tokens should now have been used.
}



// Use a valid working index and data pointer vector to create an evaluable Operation.
bool ConditionSet::Expression::SubExpression::AddOperation(vector<int> &data, size_t &index, const size_t &opIndex)
{
	// Obtain the operand indices. The operator is never a parentheses. The
	// operator index never exceeds the size of the tokens vector.
	size_t leftIndex = FindOperandIndex(tokens, operators, data, opIndex, true);
	size_t rightIndex = FindOperandIndex(tokens, operators, data, opIndex, false);
	
	// Bail out if the pointed token is in-bounds and empty.
	if((leftIndex < tokens.size() && tokens.at(leftIndex).empty())
			|| (rightIndex < tokens.size() && tokens.at(rightIndex).empty()))
	{
		Files::LogError("Unable to obtain valid operand for function \"" + operators.at(opIndex) + "\" with tokens:");
		PrintConditionError(tokens);
		tokens.clear();
		operators.clear();
		sequence.clear();
		return false;
	}
	
	// Record use of an operand by writing where its latest value is found.
	data.at(leftIndex) = index;
	data.at(rightIndex) = index;
	// Create the Operation.
	sequence.emplace_back(operators.at(opIndex), leftIndex, rightIndex);
	// Update the pointed index for the next operation.
	++index;
	
	return true;
}



// Constructor for an Operation, indicating the binary function and the
// indices of its operands within the evaluation-time data vector.
ConditionSet::Expression::SubExpression::Operation::Operation(const string &op, size_t &a, size_t &b)
	: fun(Op(op)), a(a), b(b)
{
}


// Converts the given vector of condition tokens (like "reputation: Republic",
// "random", or "4") into the integral values they have at runtime.
vector<int64_t> ConditionSet::Expression::SubExpression::SubstituteValues(const vector<string> &side, const map<string, int64_t> &conditions, const map<string, int64_t> &created) const
{
	auto result = vector<int64_t>();
	std::string temp;
	auto bracketExpression = bracketExpressions.begin();
	result.reserve(side.size());
	for(const string &in_str : side)
	{
		int64_t value = 0;
		const std::string *str = &in_str;
		// if a bracket expression is involved here, evaluate and apply...
		if(bracketExpression != bracketExpressions.end()
				&& bracketExpression->first == result.size()) {
			ostringstream s;
			s << in_str << " [" << bracketExpression->second.Evaluate(conditions, created) << "]";
			temp = s.str();
			str = &temp;
			++bracketExpression;
		}
		if(*str == "random")
			value = Random::Int(100);
		else if(DataNode::IsNumber(*str))
			value = static_cast<int64_t>(DataNode::Value(*str));
		else
		{
			const auto temp = created.find(*str);
			const auto perm = conditions.find(*str);
			if(temp != created.end())
				value = temp->second;
			else if(perm != conditions.end())
				value = perm->second;
		}
		result.emplace_back(value);
	}
	return result;
}

std::string ConditionSet::Expression::SubExpression::GetConditionName(const Conditions &conditions, const Conditions &created) const
{
	if(tokens.empty())
		return ""; // should not happen
	else if(bracketExpressions.empty())
		return tokens.at(0);
	else
	{
		if(bracketExpressions.size() != 1 || bracketExpressions.front().first != 0) {
			Files::LogError("Weird, malformed bracket expression in assignment");
			return "";
		}
		ostringstream s;
		s << tokens.at(0) << " [" << bracketExpressions.front().second.Evaluate(conditions, created) << "]";
		return s.str();
	}
}

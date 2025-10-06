#!/usr/bin/env python3
"""
Parse Lean files to extract theorem definitions and their dependencies,
then generate a GraphViz DOT format dependency graph.
"""

import re
import os
from pathlib import Path
from typing import Dict, List, Set, Tuple
import argparse

class TheoremParser:
    def __init__(self):
        self.theorems = {}  # theorem_name -> file_path
        self.dependencies = {}  # theorem_name -> set of referenced theorems
        self.theorem_content = {}  # theorem_name -> content
        
    def parse_file(self, file_path: str) -> None:
        """Parse a Lean file to extract theorems and their dependencies."""
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Remove comments first
        content = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)
        content = re.sub(r'--.*$', '', content, flags=re.MULTILINE)
        
        # Find all theorem definitions - improved pattern
        theorem_pattern = r'theorem\s+([a-zA-Z][a-zA-Z0-9_\'\.]*)'
        
        # First pass: find all theorem names
        for match in re.finditer(theorem_pattern, content):
            theorem_name = match.group(1)
            self.theorems[theorem_name] = file_path
        
        # Second pass: extract theorem bodies and dependencies
        lines = content.split('\n')
        current_theorem = None
        theorem_body_lines = []
        in_theorem = False
        
        for line in lines:
            line = line.strip()
            
            # Check if this line starts a theorem
            theorem_match = re.match(r'theorem\s+([a-zA-Z][a-zA-Z0-9_\'\.]*)', line)
            if theorem_match:
                # Save previous theorem if any
                if current_theorem and theorem_body_lines:
                    theorem_body = '\n'.join(theorem_body_lines)
                    self.theorem_content[current_theorem] = theorem_body
                    dependencies = self.extract_dependencies(theorem_body)
                    self.dependencies[current_theorem] = dependencies
                
                # Start new theorem
                current_theorem = theorem_match.group(1)
                theorem_body_lines = [line]
                in_theorem = True
                continue
            
            # Check if we're ending a theorem
            if in_theorem and (line.startswith('theorem ') or line.startswith('def ') or 
                               line.startswith('lemma ') or line.startswith('example ') or
                               line.startswith('#') or line.startswith('end ') or
                               line.startswith('namespace ') or line.startswith('open ')):
                # End current theorem
                if current_theorem and theorem_body_lines:
                    theorem_body = '\n'.join(theorem_body_lines)
                    self.theorem_content[current_theorem] = theorem_body
                    dependencies = self.extract_dependencies(theorem_body)
                    self.dependencies[current_theorem] = dependencies
                in_theorem = False
                current_theorem = None
                theorem_body_lines = []
                
                # Check if this line starts a new theorem
                theorem_match = re.match(r'theorem\s+([a-zA-Z][a-zA-Z0-9_\'\.]*)', line)
                if theorem_match:
                    current_theorem = theorem_match.group(1)
                    theorem_body_lines = [line]
                    in_theorem = True
                continue
            
            # Add line to current theorem body
            if in_theorem:
                theorem_body_lines.append(line)
        
        # Handle the last theorem
        if current_theorem and theorem_body_lines:
            theorem_body = '\n'.join(theorem_body_lines)
            self.theorem_content[current_theorem] = theorem_body
            dependencies = self.extract_dependencies(theorem_body)
            self.dependencies[current_theorem] = dependencies
    
    def extract_dependencies(self, theorem_body: str) -> Set[str]:
        """Extract theorem names referenced in the proof."""
        dependencies = set()
        
        # Look for exact theorem references by name
        # Pattern for theorem calls like 'exact theorem_name', 'apply theorem_name', etc.
        call_patterns = [
            r'(?:exact|apply|refine|rw|simp\s*\[|have.*:=)\s+([a-zA-Z][a-zA-Z0-9_\'\.]*)',
            r'(?:by\s+exact|by\s+apply|by\s+refine)\s+([a-zA-Z][a-zA-Z0-9_\'\.]*)',
            r'([A-Z][a-zA-Z0-9_]*\.[a-zA-Z][a-zA-Z0-9_\']*)',  # Qualified names like LubyTree.depth_gt_one
            r'([a-z][a-zA-Z0-9_]*_[a-zA-Z0-9_]*)',  # Names with underscores like luby_value_at_segment_beg
        ]
        
        for pattern in call_patterns:
            for match in re.finditer(pattern, theorem_body):
                name = match.group(1)
                # Filter out common Lean keywords and tactics
                if not self.is_lean_keyword(name) and len(name) > 2:
                    dependencies.add(name)
        
        return dependencies
    
    def is_lean_keyword(self, name: str) -> bool:
        """Check if a name is a Lean keyword or common tactic."""
        keywords = {
            'by', 'exact', 'apply', 'simp', 'rw', 'grind', 'omega', 'constructor',
            'intro', 'intros', 'split', 'cases', 'induction', 'have', 'show',
            'calc', 'use', 'refine', 'ring', 'field', 'linarith', 'nlinarith',
            'norm_num', 'norm_cast', 'congr', 'ext', 'funext', 'left', 'right',
            'contradiction', 'absurd', 'exfalso', 'sorry', 'admit', 'done',
            'rfl', 'refl', 'symm', 'trans', 'true', 'false', 'and', 'or',
            'not', 'iff', 'exists', 'forall', 'fun', 'let', 'in', 'if', 'then',
            'else', 'match', 'with', 'end', 'do', 'return', 'where', 'this',
            'that', 'it', 'goal', 'assumption', 'trivial', 'decide', 'value_of',
            'expose_names', 'clear', 'simp_all', 'tauto', 'finish', 'step1',
            'step2', 'step3', 'goal1', 'goal2', 'goal3', 'left1', 'right1',
            'ap', 'bp', 'cp', 'dp', 'hp', 'mp', 'np', 'op', 'pp', 'qp', 'rp',
            'sp', 'tp', 'up', 'vp', 'wp', 'xp', 'yp', 'zp', 'sub', 'add',
            'mul', 'div', 'mod', 'pow', 'neg', 'abs', 'min', 'max', 'zero',
            'one', 'two', 'self', 'id', 'eq', 'ne', 'lt', 'le', 'gt', 'ge',
            'Nat', 'Int', 'Bool', 'List', 'String', 'Option', 'default',
            'succ', 'pred', 'add', 'sub', 'mul', 'div', 'mod', 'pow',
            'Eq', 'Ne', 'Lt', 'Le', 'Gt', 'Ge', 'HAdd', 'HSub', 'HMul',
            'HDiv', 'HMod', 'HPow', 'Dvd', 'Even', 'Odd'
        }
        base_name = name.split('.')[-1].lower()
        return base_name in keywords or len(name) <= 2 or name.isdigit()
    
    def filter_actual_theorems(self) -> None:
        """Filter dependencies to only include actual theorems we found."""
        for theorem_name in self.dependencies:
            # Only keep dependencies that are actual theorems in our files
            actual_deps = set()
            for dep in self.dependencies[theorem_name]:
                # Check if this dependency is a theorem we found
                base_name = dep.split('.')[-1]  # Get the last part after dots
                if dep in self.theorems:
                    actual_deps.add(dep)
                elif base_name in self.theorems and base_name != theorem_name:  # Avoid self-references
                    actual_deps.add(base_name)
            self.dependencies[theorem_name] = actual_deps
    
    def generate_dot_graph(self, output_file: str = 'graph.dot') -> None:
        """Generate a GraphViz DOT format file."""
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write('digraph TheoremDependencies {\n')
            f.write('  rankdir=TB;\n')
            f.write('  compound=true;\n')
            f.write('  node [shape=box, style=filled, fillcolor=lightblue, fontname="Arial"];\n')
            f.write('  edge [color=blue, arrowhead=vee];\n\n')
            
            # Group theorems by file
            file_groups = {}
            for theorem, file_path in self.theorems.items():
                file_name = os.path.basename(file_path).replace('.lean', '')
                if file_name not in file_groups:
                    file_groups[file_name] = []
                file_groups[file_name].append(theorem)
            
            # Define colors for different files
            colors = ['lightcyan', 'lightpink', 'lightgreen', 'lightyellow', 'lavender']
            
            # Create subgraphs for each file
            for i, (file_name, theorems) in enumerate(file_groups.items()):
                color = colors[i % len(colors)]
                f.write(f'  subgraph cluster_{file_name} {{\n')
                f.write(f'    label="{file_name}.lean";\n')
                f.write('    style=filled;\n')
                f.write(f'    fillcolor={color};\n')
                f.write('    fontname="Arial Bold";\n')
                f.write('    fontsize=12;\n')
                for theorem in sorted(theorems):  # Sort for consistent ordering
                    # Escape theorem names that might contain dots
                    escaped_name = theorem.replace('.', '_')
                    f.write(f'    "{escaped_name}" [label="{theorem}"];\n')
                f.write('  }\n\n')
            
            # Add dependency edges (excluding self-references)
            edge_count = 0
            for theorem, deps in self.dependencies.items():
                escaped_theorem = theorem.replace('.', '_')
                for dep in deps:
                    if dep != theorem and dep in self.theorems:  # Avoid self-references
                        escaped_dep = dep.replace('.', '_')
                        f.write(f'  "{escaped_theorem}" -> "{escaped_dep}";\n')
                        edge_count += 1
            
            f.write('}\n')
        
        print(f"Generated dependency graph in {output_file}")
        print(f"Graph contains {len(self.theorems)} theorems and {edge_count} dependency edges")
    
    def print_stats(self) -> None:
        """Print statistics about the theorems and dependencies."""
        total_theorems = len(self.theorems)
        total_deps = sum(len(deps) for deps in self.dependencies.values())
        
        print(f"Found {total_theorems} theorems")
        print(f"Total dependencies: {total_deps}")
        
        # Most referenced theorems
        ref_count = {}
        for deps in self.dependencies.values():
            for dep in deps:
                ref_count[dep] = ref_count.get(dep, 0) + 1
        
        if ref_count:
            most_ref = sorted(ref_count.items(), key=lambda x: x[1], reverse=True)[:5]
            print("\nMost referenced theorems:")
            for theorem, count in most_ref:
                if theorem in self.theorems:
                    print(f"  {theorem}: {count} references")

def main():
    parser = argparse.ArgumentParser(description='Parse Lean theorems and generate dependency graph')
    parser.add_argument('--directory', '-d', default='LubySequence', 
                       help='Directory containing Lean files')
    parser.add_argument('--output', '-o', default='graph.dot',
                       help='Output DOT file name')
    
    args = parser.parse_args()
    
    theorem_parser = TheoremParser()
    
    # Parse all .lean files in the directory
    lean_dir = Path(args.directory)
    if not lean_dir.exists():
        print(f"Directory {args.directory} does not exist")
        return
    
    lean_files = list(lean_dir.glob('*.lean'))
    if not lean_files:
        print(f"No .lean files found in {args.directory}")
        return
    
    print(f"Parsing {len(lean_files)} Lean files...")
    for lean_file in lean_files:
        print(f"  Parsing {lean_file}")
        theorem_parser.parse_file(str(lean_file))
    
    # Filter to only actual theorem dependencies
    theorem_parser.filter_actual_theorems()
    
    # Generate output
    theorem_parser.print_stats()
    theorem_parser.generate_dot_graph(args.output)

if __name__ == '__main__':
    main()
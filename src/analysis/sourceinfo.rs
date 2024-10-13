use std::fs::File;
use std::io::{BufRead, BufReader};

use regex::Regex;

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub struct SourceInfo {
    file_path: String,
    start_line: usize,
    start_column: usize,
    end_line: usize,
    end_column: usize,
}

impl SourceInfo {
    pub fn from_span(span: rustc_span::Span, re: &Regex) -> Self {
        let span_str = format!("{:?}", span);
        let caps = re.captures(&span_str).unwrap();

        let file_path = caps.get(1).map_or("", |m| m.as_str());
        let start_line = caps.get(2).map_or("", |m| m.as_str());
        let start_column = caps.get(3).map_or("", |m| m.as_str());
        let end_line = caps.get(4).map_or("", |m| m.as_str());
        let end_column = caps.get(5).map_or("", |m| m.as_str());

        SourceInfo {
            file_path: file_path.to_string(),
            start_line: start_line.parse::<usize>().unwrap(),
            start_column: start_column.parse::<usize>().unwrap(),
            end_line: end_line.parse::<usize>().unwrap(),
            end_column: end_column.parse::<usize>().unwrap(),
        }
    }

    pub fn get_string(&self) -> String {
        let file = File::open(&self.file_path).unwrap();
        let reader = BufReader::new(file);

        let mut result = String::new();
        for (line_number, line) in reader.lines().enumerate() {
            let line_number = line_number + 1; // Convert to 1-based index
            let line = line.unwrap();
            if line_number < self.start_line {
                continue;
            }
            if line_number > self.end_line {
                break;
            }
            let start_col = if line_number == self.start_line {
                self.start_column - 1
            } else {
                0
            };
            let end_col = if line_number == self.end_line {
                self.end_column - 1
            } else {
                line.len()
            };
            if start_col <= end_col && end_col <= line.len() {
                let snippet = line
                    .chars()
                    .skip(start_col)
                    .take(end_col - start_col)
                    .collect::<String>();
                result.push_str(&snippet);
            }
            if line_number < self.end_line {
                result.push('\n');
            }
        }
        result
    }

    pub fn substring_source_info(&self, start: usize, length: usize) -> SourceInfo {
        let original = self.get_string();
        let substring = &original[start..start + length];
        let mut current_line = self.start_line;
        let mut current_column = self.start_column;

        // Calculate the starting line and column for the substring
        for (_, c) in original[..start].chars().enumerate() {
            if c == '\n' {
                current_line += 1;
                current_column = 1;
            } else {
                current_column += 1;
            }
        }
        let start_line = current_line;
        let start_column = current_column;
        // Calculate the ending line and column for the substring
        for c in substring.chars() {
            if c == '\n' {
                current_line += 1;
                current_column = 1;
            } else {
                current_column += 1;
            }
        }
        let end_line = current_line;
        let end_column = current_column;
        SourceInfo {
            file_path: self.file_path.clone(),
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }

    pub fn contains(&self, other: &SourceInfo) -> bool {
        // Ensure the file paths are the same
        if self.file_path != other.file_path {
            return false;
        }

        // Check if the start position of `other` is after or at the start of `self`
        let start_within = (other.start_line > self.start_line)
            || (other.start_line == self.start_line && other.start_column >= self.start_column);

        // Check if the end position of `other` is before or at the end of `self`
        let end_within = (other.end_line < self.end_line)
            || (other.end_line == self.end_line && other.end_column <= self.end_column);

        start_within && end_within
    }

    pub fn expand(&self, other: &SourceInfo) -> Option<SourceInfo> {
        // Ensure the file paths are the same
        if self.file_path != other.file_path {
            return None;
        }

        // Determine the earliest start position
        let (start_line, start_column) = if (self.start_line < other.start_line)
            || (self.start_line == other.start_line && self.start_column <= other.start_column)
        {
            (self.start_line, self.start_column)
        } else {
            (other.start_line, other.start_column)
        };

        // Determine the latest end position
        let (end_line, end_column) = if (self.end_line > other.end_line)
            || (self.end_line == other.end_line && self.end_column >= other.end_column)
        {
            (self.end_line, self.end_column)
        } else {
            (other.end_line, other.end_column)
        };

        Some(SourceInfo {
            file_path: self.file_path.clone(),
            start_line,
            start_column,
            end_line,
            end_column,
        })
    }
}

# Talk Timer Specification

A talk rehearsal timer that tracks lap times, organizes takes by section, and computes optimal talk duration.

## Feature: Timer Core Logic

- [verified] Timer displays elapsed time in minutes and seconds format (MM:SS)
- [verified] A single tap or keypress creates a lap marker at the current elapsed time
- [verified] Each lap records the duration from the previous lap marker (or start) to the current marker

## Feature: Session Data Model

- [verified] Sessions are organized hierarchically: a Talk contains Sections, each Section contains one or more Takes
- [verified] Each lap can be labeled with a section name after it is recorded
- [verified] All takes are preserved with their timestamps and durations

## Feature: Take Selection & Assembly

- [verified] Users can manually select which takes to include in the final talk total
- [verified] Users can delete unwanted or noisy takes (without affecting other takes' durations)
- [verified] Users can manually adjust the duration of any take
- [verified] Total estimated talk duration is computed by summing the selected takes

## Feature: Undo/Redo System

- [verified] All lap, label, select, and delete actions support undo and redo operations
- [verified] The undo/redo stack preserves complete action history for the session

## Feature: User Interface

- [trusted] The app provides a translucent overlay mode that stays visible but unobtrusive during rehearsal
- [trusted] Visual design uses soft muted colors for minimal distraction
- [trusted] A soft visual indicator shows progress toward a target talk duration when set
- [trusted] Sessions can be exported as Markdown summaries

## Feature: Keyboard & Accessibility

- [trusted] All primary functions are accessible via keyboard shortcuts for hands-free operation
- [trusted] The app can be quickly shown and hidden during rehearsal

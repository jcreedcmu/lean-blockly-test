import type { TutorialStep } from '../gameData';

const tutorial: TutorialStep[] = [
  {
    target: '.world-3d-container',
    title: 'Welcome to Real Analysis, The Game!',
    content: 'This tutorial will show you around.',
    placement: 'center',
  },
  {
    target: '.world-3d-why-btn',
    content: 'Want to know what our Course - ahem, Game - is all about? Click on "Why Real Analysis?".',
    placement: 'bottom',
  },
  {
    target: '.world-3d-reset-btn',
    content: 'If you want to reset the browser and start all over, click this reset button.',
    placement: 'left',
  },
  {
    target: '.world-3d-help-btn',
    content: 'And if you want to see this tutorial again, click on this Question Mark.',
    placement: 'left',
  },
  {
    target: '.world-3d-first-world-anchor',
    content: 'When you are ready to play, click on the Tutorial World to get started.  Enjoy the Game!',
    placement: 'bottom',
  },
];

export default tutorial;
